#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

#define BIGINT_BASE 256U
#define BIGINT_DIGIT_MASK 0xFFU
#define BIGINT_SIGN_BIT 0x80000000U
#define KARATSUBA_THRESHOLD 32

typedef struct {
    int msd;               // старшая цифра + знак в старшем бите
    unsigned int *data;    // data[0] = число цифр, data[1..n] = цифры little-endian
} BigInt;

typedef BigInt (*mul_fn)(const BigInt*, const BigInt*);

/* ========================= ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ========================= */

static void die(const char *msg) {
    fprintf(stderr, "Ошибка: %s\n", msg);
    exit(EXIT_FAILURE);
}

static unsigned int bigint_abs_msd(const BigInt *a) {
    return ((unsigned int)a->msd) & (~BIGINT_SIGN_BIT);
}

static int bigint_sign(const BigInt *a) {
    return ((((unsigned int)a->msd) & BIGINT_SIGN_BIT) != 0U) ? -1 : 1;
}

static void bigint_set_sign(BigInt *a, int sign) {
    unsigned int abs_msd = bigint_abs_msd(a);
    if (sign < 0 && !(a->data[0] == 1 && a->data[1] == 0)) {
        a->msd = (int)(abs_msd | BIGINT_SIGN_BIT);
    } else {
        a->msd = (int)abs_msd;
    }
}

static int bigint_is_zero(const BigInt *a) {
    return (a->data[0] == 1 && a->data[1] == 0);
}

static BigInt bigint_init_zero(void) {
    BigInt a;
    a.data = (unsigned int*)malloc(2 * sizeof(unsigned int));
    if (!a.data) die("Не удалось выделить память");
    a.data[0] = 1;
    a.data[1] = 0;
    a.msd = 0;
    return a;
}

static void bigint_free(BigInt *a) {
    if (a && a->data) {
        free(a->data);
        a->data = NULL;
        a->msd = 0;
    }
}

static BigInt bigint_clone(const BigInt *src) {
    BigInt dst;
    unsigned int n = src->data[0];
    dst.data = (unsigned int*)malloc((n + 1) * sizeof(unsigned int));
    if (!dst.data) die("Не удалось выделить память");
    memcpy(dst.data, src->data, (n + 1) * sizeof(unsigned int));
    dst.msd = src->msd;
    return dst;
}

static void bigint_normalize(BigInt *a) {
    unsigned int n = a->data[0];
    while (n > 1 && a->data[n] == 0) {
        n--;
    }
    a->data[0] = n;

    unsigned int abs_msd = a->data[n] & BIGINT_DIGIT_MASK;
    int sign = bigint_sign(a);

    if (n == 1 && a->data[1] == 0) {
        sign = 1;
    }

    a->msd = (int)abs_msd;
    bigint_set_sign(a, sign);
}

static BigInt bigint_from_int64(long long value) {
    BigInt a = bigint_init_zero();

    unsigned long long mag;
    int sign = 1;
    if (value < 0) {
        sign = -1;
        mag = (unsigned long long)(-(value + 1)) + 1ULL;
    } else {
        mag = (unsigned long long)value;
    }

    if (mag == 0) {
        return a;
    }

    unsigned int digits[16];
    unsigned int cnt = 0;
    while (mag > 0) {
        digits[++cnt] = (unsigned int)(mag % BIGINT_BASE);
        mag /= BIGINT_BASE;
    }

    free(a.data);
    a.data = (unsigned int*)malloc((cnt + 1) * sizeof(unsigned int));
    if (!a.data) die("Не удалось выделить память");

    a.data[0] = cnt;
    for (unsigned int i = 1; i <= cnt; i++) {
        a.data[i] = digits[i];
    }

    a.msd = (int)(a.data[cnt] & BIGINT_DIGIT_MASK);
    bigint_set_sign(&a, sign);
    bigint_normalize(&a);
    return a;
}

static void bigint_print_hex(const BigInt *a) {
    if (bigint_sign(a) < 0 && !bigint_is_zero(a)) {
        printf("-");
    }
    unsigned int n = a->data[0];
    printf("0x");
    printf("%X", a->data[n]);
    for (int i = (int)n - 1; i >= 1; i--) {
        printf("%02X", a->data[i]);
    }
}

static long long bigint_to_int64_safe(const BigInt *a, int *ok) {
    unsigned int n = a->data[0];
    if (n > 8) {
        *ok = 0;
        return 0;
    }

    unsigned long long val = 0;
    for (int i = (int)n; i >= 1; i--) {
        val = val * BIGINT_BASE + a->data[i];
    }

    if (bigint_sign(a) < 0) {
        if (val > (unsigned long long)INT64_MAX + 1ULL) {
            *ok = 0;
            return 0;
        }
        *ok = 1;
        if (val == (unsigned long long)INT64_MAX + 1ULL) {
            return INT64_MIN;
        }
        return -(long long)val;
    }

    if (val > (unsigned long long)INT64_MAX) {
        *ok = 0;
        return 0;
    }

    *ok = 1;
    return (long long)val;
}

static int bigint_cmp_abs(const BigInt *a, const BigInt *b) {
    unsigned int na = a->data[0];
    unsigned int nb = b->data[0];

    if (na != nb) {
        return (na > nb) ? 1 : -1;
    }

    for (int i = (int)na; i >= 1; i--) {
        if (a->data[i] != b->data[i]) {
            return (a->data[i] > b->data[i]) ? 1 : -1;
        }
    }
    return 0;
}

/* ========================= СЛОЖЕНИЕ / ВЫЧИТАНИЕ ========================= */

static BigInt bigint_add_abs(const BigInt *a, const BigInt *b) {
    unsigned int na = a->data[0];
    unsigned int nb = b->data[0];
    unsigned int nmax = (na > nb) ? na : nb;

    BigInt res;
    res.data = (unsigned int*)calloc(nmax + 2, sizeof(unsigned int));
    if (!res.data) die("Не удалось выделить память");

    unsigned int carry = 0;
    for (unsigned int i = 1; i <= nmax; i++) {
        unsigned int da = (i <= na) ? a->data[i] : 0;
        unsigned int db = (i <= nb) ? b->data[i] : 0;
        unsigned int sum = da + db + carry;
        res.data[i] = sum & BIGINT_DIGIT_MASK;
        carry = sum / BIGINT_BASE;
    }

    res.data[0] = nmax;
    if (carry) {
        res.data[++res.data[0]] = carry;
    }

    res.msd = (int)res.data[res.data[0]];
    bigint_set_sign(&res, 1);
    bigint_normalize(&res);
    return res;
}

static BigInt bigint_sub_abs(const BigInt *a, const BigInt *b) {
    /* Предполагается |a| >= |b| */
    BigInt res;
    unsigned int na = a->data[0];
    unsigned int nb = b->data[0];

    res.data = (unsigned int*)calloc(na + 1, sizeof(unsigned int));
    if (!res.data) die("Не удалось выделить память");

    int borrow = 0;
    for (unsigned int i = 1; i <= na; i++) {
        int da = (int)a->data[i];
        int db = (i <= nb) ? (int)b->data[i] : 0;
        int diff = da - db - borrow;
        if (diff < 0) {
            diff += (int)BIGINT_BASE;
            borrow = 1;
        } else {
            borrow = 0;
        }
        res.data[i] = (unsigned int)diff;
    }

    res.data[0] = na;
    res.msd = (int)res.data[na];
    bigint_set_sign(&res, 1);
    bigint_normalize(&res);
    return res;
}

static BigInt bigint_add_new(const BigInt *a, const BigInt *b) {
    int sa = bigint_sign(a);
    int sb = bigint_sign(b);

    if (sa == sb) {
        BigInt res = bigint_add_abs(a, b);
        bigint_set_sign(&res, sa);
        bigint_normalize(&res);
        return res;
    }

    int cmp = bigint_cmp_abs(a, b);
    if (cmp == 0) {
        return bigint_init_zero();
    } else if (cmp > 0) {
        BigInt res = bigint_sub_abs(a, b);
        bigint_set_sign(&res, sa);
        bigint_normalize(&res);
        return res;
    } else {
        BigInt res = bigint_sub_abs(b, a);
        bigint_set_sign(&res, sb);
        bigint_normalize(&res);
        return res;
    }
}

static BigInt bigint_negated(const BigInt *a) {
    BigInt res = bigint_clone(a);
    if (!bigint_is_zero(&res)) {
        bigint_set_sign(&res, -bigint_sign(&res));
    }
    return res;
}

static BigInt bigint_sub_new(const BigInt *a, const BigInt *b) {
    BigInt nb = bigint_negated(b);
    BigInt res = bigint_add_new(a, &nb);
    bigint_free(&nb);
    return res;
}

static void bigint_add_inplace(BigInt *a, const BigInt *b) {
    BigInt res = bigint_add_new(a, b);
    bigint_free(a);
    *a = res;
}

static void bigint_sub_inplace(BigInt *a, const BigInt *b) {
    BigInt res = bigint_sub_new(a, b);
    bigint_free(a);
    *a = res;
}

/* ========================= СДВИГИ И СРЕЗЫ ========================= */

static BigInt bigint_shift_digits(const BigInt *a, unsigned int k) {
    if (bigint_is_zero(a)) {
        return bigint_init_zero();
    }

    unsigned int n = a->data[0];
    BigInt res;
    res.data = (unsigned int*)calloc(n + k + 1, sizeof(unsigned int));
    if (!res.data) die("Не удалось выделить память");

    res.data[0] = n + k;
    for (unsigned int i = 1; i <= n; i++) {
        res.data[i + k] = a->data[i];
    }

    res.msd = (int)res.data[res.data[0]];
    bigint_set_sign(&res, bigint_sign(a));
    bigint_normalize(&res);
    return res;
}

static BigInt bigint_slice_abs(const BigInt *a, unsigned int start, unsigned int len) {
    BigInt res = bigint_init_zero();
    unsigned int n = a->data[0];

    if (start > n || len == 0) {
        return res;
    }

    unsigned int end = start + len - 1;
    if (end > n) end = n;

    unsigned int real_len = end - start + 1;
    free(res.data);
    res.data = (unsigned int*)calloc(real_len + 1, sizeof(unsigned int));
    if (!res.data) die("Не удалось выделить память");

    res.data[0] = real_len;
    for (unsigned int i = 0; i < real_len; i++) {
        res.data[i + 1] = a->data[start + i];
    }

    res.msd = (int)res.data[real_len];
    bigint_set_sign(&res, 1);
    bigint_normalize(&res);
    return res;
}

/* ========================= Факториал ========================= */

static BigInt bigint_factorial(unsigned int n, mul_fn mul) {
    BigInt res = bigint_from_int64(1);

    for (unsigned int i = 2; i <= n; i++) {
        BigInt t = bigint_from_int64((long long)i);
        BigInt tmp = mul(&res, &t);
        bigint_free(&res);
        bigint_free(&t);
        res = tmp;
    }

    return res;
}

static BigInt bigint_af(unsigned int n, mul_fn mul) {
    if (n % 2 == 0) {
        return bigint_init_zero();
    }
    return bigint_factorial(n, mul);
}

/* ========================= УМНОЖЕНИЕ В СТОЛБИК ========================= */

static BigInt bigint_mul_column(const BigInt *a, const BigInt *b) {
    if (bigint_is_zero(a) || bigint_is_zero(b)) {
        return bigint_init_zero();
    }

    unsigned int na = a->data[0];
    unsigned int nb = b->data[0];

    BigInt res;
    res.data = (unsigned int*)calloc(na + nb + 1, sizeof(unsigned int));
    if (!res.data) die("Не удалось выделить память");

    for (unsigned int i = 1; i <= na; i++) {
        unsigned int carry = 0;
        for (unsigned int j = 1; j <= nb; j++) {
            unsigned int idx = i + j - 1;
            unsigned int cur = res.data[idx] + a->data[i] * b->data[j] + carry;
            res.data[idx] = cur & BIGINT_DIGIT_MASK;
            carry = cur / BIGINT_BASE;
        }

        unsigned int idx = i + nb;
        while (carry) {
            unsigned int cur = res.data[idx] + carry;
            res.data[idx] = cur & BIGINT_DIGIT_MASK;
            carry = cur / BIGINT_BASE;
            idx++;
        }
    }

    res.data[0] = na + nb;
    res.msd = (int)res.data[res.data[0]];
    bigint_set_sign(&res, bigint_sign(a) * bigint_sign(b));
    bigint_normalize(&res);
    return res;
}

static void bigint_mul_column_inplace(BigInt *a, const BigInt *b) {
    BigInt res = bigint_mul_column(a, b);
    bigint_free(a);
    *a = res;
}

/* ========================= КАРАЦУБА ========================= */

static BigInt bigint_mul_karatsuba_abs(const BigInt *x, const BigInt *y) {
    unsigned int nx = x->data[0];
    unsigned int ny = y->data[0];
    unsigned int n = (nx > ny) ? nx : ny;

    if (bigint_is_zero(x) || bigint_is_zero(y)) {
        return bigint_init_zero();
    }

    if (n <= KARATSUBA_THRESHOLD) {
        BigInt xx = bigint_clone(x);
        BigInt yy = bigint_clone(y);
        bigint_set_sign(&xx, 1);
        bigint_set_sign(&yy, 1);
        BigInt r = bigint_mul_column(&xx, &yy);
        bigint_free(&xx);
        bigint_free(&yy);
        bigint_set_sign(&r, 1);
        return r;
    }

    unsigned int m = n / 2;

    BigInt x0 = bigint_slice_abs(x, 1, m);
    BigInt x1 = bigint_slice_abs(x, m + 1, nx - m);
    BigInt y0 = bigint_slice_abs(y, 1, m);
    BigInt y1 = bigint_slice_abs(y, m + 1, ny - m);

    BigInt z0 = bigint_mul_karatsuba_abs(&x0, &y0);
    BigInt z2 = bigint_mul_karatsuba_abs(&x1, &y1);

    BigInt x0x1 = bigint_add_abs(&x0, &x1);
    BigInt y0y1 = bigint_add_abs(&y0, &y1);

    BigInt z1 = bigint_mul_karatsuba_abs(&x0x1, &y0y1);

    BigInt tmp = bigint_sub_new(&z1, &z2);
    bigint_free(&z1);
    z1 = bigint_sub_new(&tmp, &z0);
    bigint_free(&tmp);

    BigInt z2_shift = bigint_shift_digits(&z2, 2 * m);
    BigInt z1_shift = bigint_shift_digits(&z1, m);
    BigInt part = bigint_add_new(&z2_shift, &z1_shift);
    BigInt res = bigint_add_new(&part, &z0);

    bigint_free(&x0);
    bigint_free(&x1);
    bigint_free(&y0);
    bigint_free(&y1);
    bigint_free(&z0);
    bigint_free(&z1);
    bigint_free(&z2);
    bigint_free(&x0x1);
    bigint_free(&y0y1);
    bigint_free(&z2_shift);
    bigint_free(&z1_shift);
    bigint_free(&part);

    bigint_set_sign(&res, 1);
    bigint_normalize(&res);
    return res;
}

static BigInt bigint_mul_karatsuba(const BigInt *a, const BigInt *b) {
    if (bigint_is_zero(a) || bigint_is_zero(b)) {
        return bigint_init_zero();
    }

    BigInt aa = bigint_clone(a);
    BigInt bb = bigint_clone(b);
    bigint_set_sign(&aa, 1);
    bigint_set_sign(&bb, 1);

    BigInt res = bigint_mul_karatsuba_abs(&aa, &bb);
    bigint_set_sign(&res, bigint_sign(a) * bigint_sign(b));
    bigint_normalize(&res);

    bigint_free(&aa);
    bigint_free(&bb);
    return res;
}

/* ========================= MOD 2^n ========================= */

static BigInt bigint_mod_pow2(const BigInt *a, unsigned int n_bits) {
    if (bigint_sign(a) < 0) {
        /* Для лабы сейчас ограничимся неотрицательными в этой функции */
        return bigint_init_zero();
    }

    unsigned int full_bytes = n_bits / 8;
    unsigned int rem_bits = n_bits % 8;
    unsigned int keep_digits = full_bytes + (rem_bits ? 1 : 0);

    if (keep_digits == 0) {
        return bigint_init_zero();
    }

    BigInt res = bigint_slice_abs(a, 1, keep_digits);

    if (rem_bits != 0 && res.data[0] >= keep_digits) {
        unsigned int mask = (1U << rem_bits) - 1U;
        res.data[keep_digits] &= mask;
    }

    bigint_set_sign(&res, 1);
    bigint_normalize(&res);
    return res;
}

static BigInt bigint_mul_mod_pow2(const BigInt *a, const BigInt *b, unsigned int n_bits, mul_fn mul) {
    BigInt prod = mul(a, b);
    BigInt modded = bigint_mod_pow2(&prod, n_bits);
    bigint_free(&prod);
    return modded;
}

/* Быстрое возведение в степень: 115249^4183 mod 2^n */
static BigInt bigint_pow_mod_pow2_uint(unsigned int base_val,
                                       unsigned int exp,
                                       unsigned int n_bits,
                                       mul_fn mul) {
    BigInt result = bigint_from_int64(1);
    BigInt base = bigint_from_int64((long long)base_val);
    BigInt base_mod = bigint_mod_pow2(&base, n_bits);
    bigint_free(&base);
    base = base_mod;

    while (exp > 0) {
        if (exp & 1U) {
            BigInt tmp = bigint_mul_mod_pow2(&result, &base, n_bits, mul);
            bigint_free(&result);
            result = tmp;
        }
        exp >>= 1U;
        if (exp > 0) {
            BigInt tmp = bigint_mul_mod_pow2(&base, &base, n_bits, mul);
            bigint_free(&base);
            base = tmp;
        }
    }

    bigint_free(&base);
    return result;
}


/* ========================= ГЕНЕРАЦИЯ БОЛЬШИХ ТЕСТОВЫХ ЧИСЕЛ ========================= */

static BigInt bigint_from_hex_string(const char *hex) {
    while (*hex == ' ' || *hex == '\t' || *hex == '\n') hex++;

    int sign = 1;
    if (*hex == '-') {
        sign = -1;
        hex++;
    }

    if (hex[0] == '0' && (hex[1] == 'x' || hex[1] == 'X')) {
        hex += 2;
    }

    size_t len = strlen(hex);
    while (len > 0 && hex[0] == '0') {
        hex++;
        len--;
    }

    if (len == 0) {
        return bigint_init_zero();
    }

    unsigned int digits = (unsigned int)((len + 1) / 2);

    BigInt a;
    a.data = (unsigned int*)calloc(digits + 1, sizeof(unsigned int));
    if (!a.data) die("Не удалось выделить память");

    a.data[0] = digits;

    unsigned int idx = 1;
    for (int i = (int)len - 1; i >= 0; i -= 2) {
        unsigned int low;
        char c = hex[i];
        if (c >= '0' && c <= '9') low = (unsigned int)(c - '0');
        else if (c >= 'a' && c <= 'f') low = (unsigned int)(c - 'a' + 10);
        else if (c >= 'A' && c <= 'F') low = (unsigned int)(c - 'A' + 10);
        else die("Некорректная hex-строка");

        unsigned int high = 0;
        if (i - 1 >= 0) {
            c = hex[i - 1];
            if (c >= '0' && c <= '9') high = (unsigned int)(c - '0');
            else if (c >= 'a' && c <= 'f') high = (unsigned int)(c - 'a' + 10);
            else if (c >= 'A' && c <= 'F') high = (unsigned int)(c - 'A' + 10);
            else die("Некорректная hex-строка");
        }

        a.data[idx++] = (high << 4) | low;
    }

    a.msd = (int)a.data[a.data[0]];
    bigint_set_sign(&a, sign);
    bigint_normalize(&a);
    return a;
}

/* ========================= ДЕМОНСТРАЦИЯ И ТЕСТЫ ========================= */

static void print_bigint_line(const char *label, const BigInt *a) {
    int ok = 0;
    long long v = bigint_to_int64_safe(a, &ok);

    printf("%s = ", label);
    bigint_print_hex(a);
    if (ok) {
        printf("  (%lld)", v);
    }
    printf("\n");
}

static void demo_basic_ops(void) {
    printf("===== ДЕМОНСТРАЦИЯ БАЗОВЫХ ОПЕРАЦИЙ =====\n");

    BigInt a = bigint_from_int64(123456);
    BigInt b = bigint_from_int64(-7890);

    print_bigint_line("a", &a);
    print_bigint_line("b", &b);

    BigInt s = bigint_add_new(&a, &b);
    BigInt d = bigint_sub_new(&a, &b);
    BigInt m1 = bigint_mul_column(&a, &b);
    BigInt m2 = bigint_mul_karatsuba(&a, &b);

    print_bigint_line("a + b", &s);
    print_bigint_line("a - b", &d);
    print_bigint_line("a * b (column multiply)", &m1);
    print_bigint_line("a * b (karatsuba)", &m2);

    bigint_free(&a);
    bigint_free(&b);
    bigint_free(&s);
    bigint_free(&d);
    bigint_free(&m1);
    bigint_free(&m2);

    printf("\n");
}

static void demo_inplace_ops(void) {
    printf("===== ДЕМОНСТРАЦИЯ IN-PLACE ОПЕРАЦИЙ =====\n");

    BigInt x = bigint_from_int64(1000);
    BigInt y = bigint_from_int64(255);

    print_bigint_line("x", &x);
    print_bigint_line("y", &y);

    bigint_add_inplace(&x, &y);
    print_bigint_line("x += y", &x);

    bigint_sub_inplace(&x, &y);
    print_bigint_line("x -= y", &x);

    bigint_mul_column_inplace(&x, &y);
    print_bigint_line("x *= y (column)", &x);

    bigint_free(&x);
    bigint_free(&y);

    printf("\n");
}

static void demo_expression_3a(void) {
    printf("===== ПУНКТ 3а: af(n) =====\n");

    for (unsigned int n = 1; n <= 10; n++) {
        BigInt r1 = bigint_af(n, bigint_mul_column);
        BigInt r2 = bigint_af(n, bigint_mul_karatsuba);

        printf("n = %u\n", n);
        print_bigint_line("af(n) (school)", &r1);
        print_bigint_line("af(n) (karatsuba)", &r2);
        printf("\n");

        bigint_free(&r1);
        bigint_free(&r2);
    }
}

static void demo_mod_expression_3b(void) {
    printf("===== ПУНКТ 3б: 115249^4183 mod 2^n =====\n");

    unsigned int n_bits = 64;

    BigInt r1 = bigint_pow_mod_pow2_uint(115249U, 4183U, n_bits, bigint_mul_column);
    BigInt r2 = bigint_pow_mod_pow2_uint(115249U, 4183U, n_bits, bigint_mul_karatsuba);

    printf("n = %u\n", n_bits);
    print_bigint_line("result (column)", &r1);
    print_bigint_line("result (karatsuba)", &r2);

    bigint_free(&r1);
    bigint_free(&r2);

    printf("\n");
}

static double benchmark_mul(mul_fn mul, const BigInt *a, const BigInt *b, int repeats) {
    clock_t start = clock();

    for (int i = 0; i < repeats; i++) {
        BigInt r = mul(a, b);
        bigint_free(&r);
    }

    clock_t end = clock();
    return (double)(end - start) / CLOCKS_PER_SEC;
}

static void demo_benchmark(void) {
    printf("===== СРАВНЕНИЕ ВРЕМЕНИ УМНОЖЕНИЯ =====\n");

    BigInt a = bigint_from_hex_string("1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF");
    BigInt b = bigint_from_hex_string("FEDCBA0987654321FEDCBA0987654321FEDCBA0987654321FEDCBA0987654321");

    int repeats = 200;

    double t_column = benchmark_mul(bigint_mul_column, &a, &b, repeats);
    double t_karatsuba = benchmark_mul(bigint_mul_karatsuba, &a, &b, repeats);

    printf("Повторов: %d\n", repeats);
    printf("Сolumn multiply: %.6f sec\n", t_column);
    printf("Karatsuba : %.6f sec\n", t_karatsuba);

    bigint_free(&a);
    bigint_free(&b);

    printf("\n");
}

int main(void) {
    demo_basic_ops();
    demo_inplace_ops();
    demo_expression_3a();
    demo_mod_expression_3b();
    demo_benchmark();

    return 0;
}