/*
 * phi_syntax_check.c（改訂67）：最終式 φ の全文を、生成プログラムとは独立に一文字ずつ検査する。
 *
 *   python3 final_phi.py --stream FIFO  と組み合わせて使う（全文をディスクに置かない）：
 *     mkfifo phi.fifo
 *     ./phi_syntax_check < phi.fifo &  python3 final_phi.py --stream phi.fifo
 *
 * 検査すること（本文第 2 節の文法を、Python のコードを使わずに C で書き直したもの）：
 *   - 文字は x ′ ¬ ∧ ∀ ∈ = ( ) の 9 種だけ（UTF-8）。
 *   - 全文がちょうど一つの L-式：F ::= ( V ∈ V ) | ( V = V ) | ¬F | ( F ∧ F ) | ∀V F、V ::= x ′*。
 *     （「(」の直後が x なら原子式、そうでなければ連言。変数は ′ の並びが切れたところで終わる。）
 *   - 自由変数（束縛されていない変数の出現）の集合。
 *   - 記号数（x と ′ を含め、基本記号を 1 つずつ数える）。
 * 終了コード：式として正しく、記号数と自由変数を出力できたら 0、文法の誤りや不正な文字なら 1。
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

enum { X, P, NEG, AND, ALL, ELEM, EQ, LP, RP, END };
static const char *NAME[] = {"x", "′", "¬", "∧", "∀", "∈", "=", "(", ")", "EOF"};

static unsigned char buf[1 << 22];
static size_t blen = 0, bpos = 0;
static uint64_t nsym = 0, bytes = 0, cnt[9];

static int rawbyte(void) {
    if (bpos == blen) {
        blen = fread(buf, 1, sizeof buf, stdin);
        bpos = 0;
        if (blen == 0) return -1;
    }
    bytes++;
    return buf[bpos++];
}

static void die(const char *msg) {
    fprintf(stderr, "誤り：%s（記号 %llu 個目、%llu バイト目）\n", msg,
            (unsigned long long)nsym, (unsigned long long)bytes);
    exit(1);
}

/* UTF-8 を 9 種の記号に読み替える */
static int readsym(void) {
    int c = rawbyte();
    if (c < 0) return END;
    int t;
    if (c == 'x') t = X;
    else if (c == '=') t = EQ;
    else if (c == '(') t = LP;
    else if (c == ')') t = RP;
    else if (c == 0xC2) { if (rawbyte() != 0xAC) die("不正な文字"); t = NEG; }            /* ¬ U+00AC */
    else if (c == 0xE2) {
        int c1 = rawbyte(), c2 = rawbyte();
        if (c1 == 0x80 && c2 == 0xB2) t = P;                                            /* ′ U+2032 */
        else if (c1 == 0x88 && c2 == 0xA7) t = AND;                                     /* ∧ U+2227 */
        else if (c1 == 0x88 && c2 == 0x80) t = ALL;                                     /* ∀ U+2200 */
        else if (c1 == 0x88 && c2 == 0x88) t = ELEM;                                    /* ∈ U+2208 */
        else die("不正な文字");
    } else die("不正な文字");
    nsym++; cnt[t]++;
    return t;
}

static int peeked = -2;
static int next(void) { if (peeked != -2) { int t = peeked; peeked = -2; return t; } return readsym(); }
static int peek(void) { if (peeked == -2) peeked = readsym(); return peeked; }

/* 変数：x のあとに ′ が並ぶ。′ の個数を返す。 */
static uint64_t maxvar = 0;
static uint64_t readvar(void) {
    if (next() != X) die("変数は x で始まる");
    uint64_t k = 0;
    while (peek() == P) { next(); k++; }
    if (k > maxvar) maxvar = k;
    return k;
}

/* 束縛の数（変数番号ごと） */
static uint32_t *bound = NULL; static uint64_t boundcap = 0;
static void ensure(uint64_t v) {
    if (v < boundcap) return;
    uint64_t nc = boundcap ? boundcap : 1024;
    while (nc <= v) nc *= 2;
    bound = realloc(bound, nc * sizeof *bound);
    if (!bound) die("メモリ不足");
    memset(bound + boundcap, 0, (nc - boundcap) * sizeof *bound);
    boundcap = nc;
}
static uint64_t freevars[64]; static int nfree = 0; static int freeoverflow = 0;
static void occur(uint64_t v) {
    ensure(v);
    if (bound[v] == 0) {
        for (int i = 0; i < nfree; i++) if (freevars[i] == v) return;
        if (nfree < 64) freevars[nfree++] = v; else freeoverflow = 1;
    }
}

/* 構文解析の枠：NEG、ALL（変数番号つき）、ANDL（左の式を待つ）、ANDR（右の式を待つ） */
enum { F_NEG, F_ALL, F_ANDL, F_ANDR };
typedef struct { int kind; uint64_t v; } Frame;
static Frame *stk = NULL; static uint64_t sp = 0, cap = 0, maxdepth = 0;
static void push(int kind, uint64_t v) {
    if (sp == cap) { cap = cap ? cap * 2 : 1 << 16; stk = realloc(stk, cap * sizeof *stk); if (!stk) die("メモリ不足"); }
    stk[sp].kind = kind; stk[sp].v = v; sp++;
    if (sp > maxdepth) maxdepth = sp;
}

int main(void) {
    for (;;) {
        /* 式を一つ読み始める */
        int t = next();
        if (t == NEG) { push(F_NEG, 0); continue; }
        if (t == ALL) {
            uint64_t v = readvar();
            ensure(v); bound[v]++;
            push(F_ALL, v); continue;
        }
        if (t != LP) die("式は ¬ ∀ ( のどれかで始まる");
        if (peek() != X) { push(F_ANDL, 0); continue; }
        /* 原子式 ( u ∈ v ) / ( u = v ) */
        uint64_t u = readvar();
        int op = next();
        if (op != ELEM && op != EQ) die("原子式の中央は ∈ か =");
        uint64_t w = readvar();
        if (next() != RP) die("原子式は ) で閉じる");
        occur(u); occur(w);
        /* 式が一つ完成した：枠を閉じていく */
        for (;;) {
            if (sp == 0) {
                if (next() != END) die("式のあとに余分な記号がある");
                goto done;
            }
            Frame *f = &stk[sp - 1];
            if (f->kind == F_NEG) { sp--; continue; }
            if (f->kind == F_ALL) { bound[f->v]--; sp--; continue; }
            if (f->kind == F_ANDL) {
                if (next() != AND) die("連言の左の式のあとは ∧");
                f->kind = F_ANDR;
                break;                       /* 右の式を読む */
            }
            /* F_ANDR */
            if (next() != RP) die("連言は ) で閉じる");
            sp--;
        }
    }
done:
    printf("L-式として正しい：はい\n");
    printf("記号数 = %llu\n", (unsigned long long)nsym);
    printf("自由変数 = {");
    for (int i = 0; i < nfree; i++) {
        printf("%s", i ? ", " : "");
        printf("x"); for (uint64_t k = 0; k < freevars[i]; k++) printf("′");
    }
    printf("}%s\n", freeoverflow ? "（64 個を超えたので一部のみ）" : "");
    printf("記号ごとの数：");
    for (int k = 0; k < 9; k++) printf(" %s:%llu", NAME[k], (unsigned long long)cnt[k]);
    printf("\n入れ子の最大の深さ = %llu、変数の ′ の最大個数 = %llu、バイト数 = %llu\n",
           (unsigned long long)maxdepth, (unsigned long long)maxvar, (unsigned long long)bytes);
    return 0;
}
