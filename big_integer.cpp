#include "big_integer.h"
#include <algorithm>
#include <string>
#include <vector>
#include <iomanip>

void BigInteger::fix() {
    while (v.size() > 1 && v.back() == 0) {
        v.pop_back();
    }
    if (v.empty()) {
        v.push_back(0);
        neg = false;
    }
    if (v.size() == 1 && v[0] == 0) {
        neg = false;
    }
}

BigInteger::BigInteger() : neg(false) {
    v.push_back(0);
}

BigInteger::BigInteger(int val) {
    neg = (val < 0);
    long long t = std::abs((long long)val);
    if (t == 0) v.push_back(0);
    while (t > 0) {
        v.push_back(t % BASE);
        t /= BASE;
    }
    fix();
}

BigInteger::BigInteger(long long val) {
    neg = (val < 0);
    unsigned long long t = (val < 0) ? -val : val;
    if (t == 0) v.push_back(0);
    while (t > 0) {
        v.push_back(t % BASE);
        t /= BASE;
    }
    fix();
}

BigInteger::BigInteger(const std::string& s) {
    if (s.empty() || s == "0" || s == "-0") {
        neg = false;
        v.push_back(0);
        return;
    }
    int start = 0;
    if (s[0] == '-') {
        neg = true;
        start = 1;
    } else {
        neg = false;
    }
    v.clear();
    for (int i = (int)s.size() - 1; i >= start; i -= 9) {
        int val = 0;
        int m = 1;
        for (int j = i; j > i - 9 && j >= start; j--) {
            val += (s[j] - '0') * m;
            m *= 10;
        }
        v.push_back(val);
    }
    fix();
}


int BigInteger::cmp_abs(const BigInteger& b) const {
    if (v.size() != b.v.size()) {
        return (v.size() > b.v.size()) ? 1 : -1;
    }
    for (int i = (int)v.size() - 1; i >= 0; i--) {
        if (v[i] != b.v[i]) return (v[i] > b.v[i]) ? 1 : -1;
    }
    return 0;
}

bool BigInteger::operator==(const BigInteger& b) const {
    return neg == b.neg && cmp_abs(b) == 0;
}
bool BigInteger::operator!=(const BigInteger& b) const { return !(*this == b); }
bool BigInteger::operator<(const BigInteger& b) const {
    if (neg != b.neg) return neg;
    if (neg) return cmp_abs(b) > 0;
    return cmp_abs(b) < 0;
}
bool BigInteger::operator>(const BigInteger& b) const { return b < *this; }
bool BigInteger::operator<=(const BigInteger& b) const { return !(*this > b); }
bool BigInteger::operator>=(const BigInteger& b) const { return !(*this < b); }

void BigInteger::add_mod(const BigInteger& b) {
    int carry = 0;
    for (size_t i = 0; i < std::max(v.size(), b.v.size()) || carry; i++) {
        if (i == v.size()) v.push_back(0);
        long long cur = (long long)v[i] + carry + (i < b.v.size() ? b.v[i] : 0);
        v[i] = cur % BASE;
        carry = cur / BASE;
    }
}

void BigInteger::sub_mod(const BigInteger& b) {
    int carry = 0;
    for (size_t i = 0; i < b.v.size() || carry; i++) {
        long long cur = v[i] - carry - (i < b.v.size() ? b.v[i] : 0);
        carry = cur < 0;
        if (carry) cur += BASE;
        v[i] = (int)cur;
    }
    fix();
}

BigInteger& BigInteger::operator+=(const BigInteger& b) {
    if (neg == b.neg) {
        add_mod(b);
    } else {
        if (cmp_abs(b) >= 0) {
            sub_mod(b);
        } else {
            BigInteger t = b;
            std::swap(v, t.v);
            std::swap(neg, t.neg);
            sub_mod(t);
        }
    }
    return *this;
}

BigInteger& BigInteger::operator-=(const BigInteger& b) {
    if (neg != b.neg) {
        add_mod(b);
    } else {
        if (cmp_abs(b) >= 0) {
            sub_mod(b);
        } else {
            BigInteger t = b;
            std::swap(v, t.v);
            std::swap(neg, t.neg);
            sub_mod(t);
            neg = !neg;
        }
    }
    fix();
    return *this;
}

BigInteger& BigInteger::operator*=(const BigInteger& b) {
    if (is_zero() || b.is_zero()) {
        *this = BigInteger(0);
        return *this;
    }
    BigInteger res;
    res.v.assign(v.size() + b.v.size(), 0);
    res.neg = neg != b.neg;
    for (size_t i = 0; i < v.size(); i++) {
        int carry = 0;
        for (size_t j = 0; j < b.v.size() || carry; j++) {
            long long cur = res.v[i + j] + (long long)v[i] * (j < b.v.size() ? b.v[j] : 0) + carry;
            res.v[i + j] = cur % BASE;
            carry = cur / BASE;
        }
    }
    res.fix();
    *this = res;
    return *this;
}


BigInteger& BigInteger::operator/=(const BigInteger& b) {
    if (b.is_zero()) return *this;
    bool r_neg = neg != b.neg;
    BigInteger d = b; d.neg = false;
    BigInteger q, rem;
    q.v.resize(v.size());

    for (int i = (int)v.size() - 1; i >= 0; i--) {
        rem *= BASE;
        rem += v[i];
        int l = 0, r = BASE - 1, dig = 0;
        while (l <= r) {
            int m = l + (r - l) / 2;
            if (d * m <= rem) {
                dig = m; l = m + 1;
            } else {
                r = m - 1;
            }
        }
        q.v[i] = dig;
        rem -= d * dig;
    }
    q.neg = r_neg;
    q.fix();
    *this = q;
    return *this;
}

BigInteger& BigInteger::operator%=(const BigInteger& b) {
    BigInteger q = *this / b;
    *this -= (q * b);
    return *this;
}

BigInteger BigInteger::operator+(const BigInteger& b) const { return BigInteger(*this) += b; }
BigInteger BigInteger::operator-(const BigInteger& b) const { return BigInteger(*this) -= b; }
BigInteger BigInteger::operator*(const BigInteger& b) const { return BigInteger(*this) *= b; }
BigInteger BigInteger::operator/(const BigInteger& b) const { return BigInteger(*this) /= b; }
BigInteger BigInteger::operator%(const BigInteger& b) const { return BigInteger(*this) %= b; }

BigInteger BigInteger::operator-() const {
    BigInteger res = *this;
    if (!res.is_zero()) res.neg = !res.neg;
    return res;
}

BigInteger& BigInteger::operator++() { return *this += 1; }
BigInteger BigInteger::operator++(int) { BigInteger t = *this; ++(*this); return t; }
BigInteger& BigInteger::operator--() { return *this -= 1; }
BigInteger BigInteger::operator--(int) { BigInteger t = *this; --(*this); return t; }

bool BigInteger::is_zero() const { return v.size() == 1 && v[0] == 0; }
bool BigInteger::is_negative() const { return neg; }
BigInteger::operator bool() const { return !is_zero(); }

std::string BigInteger::to_string() const {
    if (is_zero()) return "0";
    std::string s = neg ? "-" : "";
    s += std::to_string(v.back());
    for (int i = (int)v.size() - 2; i >= 0; i--) {
        std::string t = std::to_string(v[i]);
        s += std::string(9 - t.size(), '0') + t;
    }
    return s;
}

std::ostream& operator<<(std::ostream& os, const BigInteger& val) {
    os << val.to_string();
    return os;
}

std::istream& operator>>(std::istream& is, BigInteger& val) {
    std::string s;
    if (is >> s) val = BigInteger(s);
    return is;
}
