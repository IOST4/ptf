const ptfAbi = {
    "lang": "javascript",
    "version": "1.0.0",
    "abi": [
    {
        "name": "can_update",
        "args": [
            "string"
        ]
    },
    {
        "name": "issue",
        "args": [
            "string",
            "string",
            "string"
        ],
        "amountLimit": [{
            "token": "*",
            "val": "unlimited"
        }]
    },
    {
        "name": "transfer",
        "args": [
            "string",
            "string",
            "string",
            "string",
            "string"
        ],
        "amountLimit": [{
            "token": "*",
            "val": "unlimited"
        }]
    },
    {
        "name": "transferFreeze",
        "args": [
            "string",
            "string",
            "string",
            "string",
            "number",
            "string"
        ],
        "amountLimit": [{
            "token": "*",
            "val": "unlimited"
        }]
    },
    {
        "name": "destroy",
        "args": [
            "string",
            "string",
            "string"
        ],
        "amountLimit": [{
            "token": "*",
            "val": "unlimited"
        }]
    },
    {
        "name": "supply",
        "args": [
            "string"
        ]
    },
    {
        "name": "totalSupply",
        "args": [
            "string"
        ]
    },
    {
        "name": "balanceOf",
        "args": [
            "string",
            "string"
        ]
    }
]
}

const name = "PTF";
const fullName = "PTF";
const decimal = 8;
const totalSupply = 90000000000;
const admin = "admin";

class SafeMath {

    mul(x, y) {
        var carry, d, e, i, k, len, pr, rm, xd, yd,
            x = this,
            Ctor = x.constructor;

        y = new Ctor(y);

        // If either is not finite...
        if (!x.d || !y.d) {

            // Return NaN if either is NaN.
            if (!x.s || !y.s) y = new Ctor(NaN);

            // Return x if y is finite and x is ±Infinity.
            // Return x if both are ±Infinity with the same sign.
            // Return NaN if both are ±Infinity with different signs.
            // Return y if x is finite and y is ±Infinity.
            else if (!x.d) y = new Ctor(y.d || x.s === y.s ? x : NaN);

            return y;
        }

        // If signs differ...
        if (x.s != y.s) {
            y.s = -y.s;
            return x.minus(y);
        }

        xd = x.d;
        yd = y.d;
        pr = Ctor.precision;
        rm = Ctor.rounding;

        // If either is zero...
        if (!xd[0] || !yd[0]) {

            // Return x if y is zero.
            // Return y if y is non-zero.
            if (!yd[0]) y = new Ctor(x);

            return external ? finalise(y, pr, rm) : y;
        }

        // x and y are finite, non-zero numbers with the same sign.

        // Calculate base 1e7 exponents.
        k = mathfloor(x.e / LOG_BASE);
        e = mathfloor(y.e / LOG_BASE);

        xd = xd.slice();
        i = k - e;

        // If base 1e7 exponents differ...
        if (i) {

            if (i < 0) {
                d = xd;
                i = -i;
                len = yd.length;
            } else {
                d = yd;
                e = k;
                len = xd.length;
            }

            // Limit number of zeros prepended to max(ceil(pr / LOG_BASE), len) + 1.
            k = Math.ceil(pr / LOG_BASE);
            len = k > len ? k + 1 : len + 1;

            if (i > len) {
                i = len;
                d.length = 1;
            }

            // Prepend zeros to equalise exponents. Note: Faster to use reverse then do unshifts.
            d.reverse();
            for (; i--;) d.push(0);
            d.reverse();
        }

        len = xd.length;
        i = yd.length;

        // If yd is longer than xd, swap xd and yd so xd points to the longer array.
        if (len - i < 0) {
            i = len;
            d = yd;
            yd = xd;
            xd = d;
        }

        // Only start adding at yd.length - 1 as the further digits of xd can be left as they are.
        for (carry = 0; i;) {
            carry = (xd[--i] = xd[i] + yd[i] + carry) / BASE | 0;
            xd[i] %= BASE;
        }

        if (carry) {
            xd.unshift(carry);
            ++e;
        }

        // Remove trailing zeros.
        // No need to check for zero, as +x + +y != 0 && -x + -y != 0
        for (len = xd.length; xd[--len] == 0;) xd.pop();

        y.d = xd;
        y.e = getBase10Exponent(xd, e);

        return external ? finalise(y, pr, rm) : y;
    }

    div(x, y) {
        function multiplyInteger(x, k, base) {
            var temp,
                carry = 0,
                i = x.length;

            for (x = x.slice(); i--;) {
                temp = x[i] * k + carry;
                x[i] = temp % base | 0;
                carry = temp / base | 0;
            }

            if (carry) x.unshift(carry);

            return x;
        }

        function compare(a, b, aL, bL) {
            var i, r;

            if (aL != bL) {
                r = aL > bL ? 1 : -1;
            } else {
                for (i = r = 0; i < aL; i++) {
                    if (a[i] != b[i]) {
                        r = a[i] > b[i] ? 1 : -1;
                        break;
                    }
                }
            }

            return r;
        }

        function subtract(a, b, aL, base) {
            var i = 0;

            // Subtract b from a.
            for (; aL--;) {
                a[aL] -= i;
                i = a[aL] < b[aL] ? 1 : 0;
                a[aL] = i * base + a[aL] - b[aL];
            }

            // Remove leading zeros.
            for (; !a[0] && a.length > 1;) a.shift();
        }

        return function (x, y, pr, rm, dp, base) {
            var cmp, e, i, k, logBase, more, prod, prodL, q, qd, rem, remL, rem0, sd, t, xi, xL, yd0,
                yL, yz,
                Ctor = x.constructor,
                sign = x.s == y.s ? 1 : -1,
                xd = x.d,
                yd = y.d;

            // Either NaN, Infinity or 0?
            if (!xd || !xd[0] || !yd || !yd[0]) {

                return new Ctor(// Return NaN if either NaN, or both Infinity or 0.
                    !x.s || !y.s || (xd ? yd && xd[0] == yd[0] : !yd) ? NaN :

                        // Return ±0 if x is 0 or y is ±Infinity, or return ±Infinity as y is 0.
                        xd && xd[0] == 0 || !yd ? sign * 0 : sign / 0);
            }

            if (base) {
                logBase = 1;
                e = x.e - y.e;
            } else {
                base = BASE;
                logBase = LOG_BASE;
                e = mathfloor(x.e / logBase) - mathfloor(y.e / logBase);
            }

            yL = yd.length;
            xL = xd.length;
            q = new Ctor(sign);
            qd = q.d = [];

            // Result exponent may be one less than e.
            // The digit array of a Decimal from toStringBinary may have trailing zeros.
            for (i = 0; yd[i] == (xd[i] || 0); i++);

            if (yd[i] > (xd[i] || 0)) e--;

            if (pr == null) {
                sd = pr = Ctor.precision;
                rm = Ctor.rounding;
            } else if (dp) {
                sd = pr + (x.e - y.e) + 1;
            } else {
                sd = pr;
            }

            if (sd < 0) {
                qd.push(1);
                more = true;
            } else {

                // Convert precision in number of base 10 digits to base 1e7 digits.
                sd = sd / logBase + 2 | 0;
                i = 0;

                // divisor < 1e7
                if (yL == 1) {
                    k = 0;
                    yd = yd[0];
                    sd++;

                    // k is the carry.
                    for (; (i < xL || k) && sd--; i++) {
                        t = k * base + (xd[i] || 0);
                        qd[i] = t / yd | 0;
                        k = t % yd | 0;
                    }

                    more = k || i < xL;

                    // divisor >= 1e7
                } else {

                    // Normalise xd and yd so highest order digit of yd is >= base/2
                    k = base / (yd[0] + 1) | 0;

                    if (k > 1) {
                        yd = multiplyInteger(yd, k, base);
                        xd = multiplyInteger(xd, k, base);
                        yL = yd.length;
                        xL = xd.length;
                    }

                    xi = yL;
                    rem = xd.slice(0, yL);
                    remL = rem.length;

                    // Add zeros to make remainder as long as divisor.
                    for (; remL < yL;) rem[remL++] = 0;

                    yz = yd.slice();
                    yz.unshift(0);
                    yd0 = yd[0];

                    if (yd[1] >= base / 2) ++yd0;

                    do {
                        k = 0;

                        // Compare divisor and remainder.
                        cmp = compare(yd, rem, yL, remL);

                        // If divisor < remainder.
                        if (cmp < 0) {

                            // Calculate trial digit, k.
                            rem0 = rem[0];
                            if (yL != remL) rem0 = rem0 * base + (rem[1] || 0);

                            // k will be how many times the divisor goes into the current remainder.
                            k = rem0 / yd0 | 0;

                            //  Algorithm:
                            //  1. product = divisor * trial digit (k)
                            //  2. if product > remainder: product -= divisor, k--
                            //  3. remainder -= product
                            //  4. if product was < remainder at 2:
                            //    5. compare new remainder and divisor
                            //    6. If remainder > divisor: remainder -= divisor, k++

                            if (k > 1) {
                                if (k >= base) k = base - 1;

                                // product = divisor * trial digit.
                                prod = multiplyInteger(yd, k, base);
                                prodL = prod.length;
                                remL = rem.length;

                                // Compare product and remainder.
                                cmp = compare(prod, rem, prodL, remL);

                                // product > remainder.
                                if (cmp == 1) {
                                    k--;

                                    // Subtract divisor from product.
                                    subtract(prod, yL < prodL ? yz : yd, prodL, base);
                                }
                            } else {

                                // cmp is -1.
                                // If k is 0, there is no need to compare yd and rem again below, so change cmp to 1
                                // to avoid it. If k is 1 there is a need to compare yd and rem again below.
                                if (k == 0) cmp = k = 1;
                                prod = yd.slice();
                            }

                            prodL = prod.length;
                            if (prodL < remL) prod.unshift(0);

                            // Subtract product from remainder.
                            subtract(rem, prod, remL, base);

                            // If product was < previous remainder.
                            if (cmp == -1) {
                                remL = rem.length;

                                // Compare divisor and new remainder.
                                cmp = compare(yd, rem, yL, remL);

                                // If divisor < new remainder, subtract divisor from remainder.
                                if (cmp < 1) {
                                    k++;

                                    // Subtract divisor from remainder.
                                    subtract(rem, yL < remL ? yz : yd, remL, base);
                                }
                            }

                            remL = rem.length;
                        } else if (cmp === 0) {
                            k++;
                            rem = [0];
                        }    // if cmp === 1, k will be 0

                        // Add the next digit, k, to the result array.
                        qd[i++] = k;

                        // Update the remainder.
                        if (cmp && rem[0]) {
                            rem[remL++] = xd[xi] || 0;
                        } else {
                            rem = [xd[xi]];
                            remL = 1;
                        }

                    } while ((xi++ < xL || rem[0] !== void 0) && sd--);

                    more = rem[0] !== void 0;
                }

                // Leading zero?
                if (!qd[0]) qd.shift();
            }

            // logBase is 1 when divide is being used for base conversion.
            if (logBase == 1) {
                q.e = e;
                inexact = more;
            } else {

                // To calculate q.e, first get the number of digits of qd[0].
                for (i = 1, k = qd[0]; k >= 10; k /= 10) i++;
                q.e = i + e * logBase - 1;

                finalise(q, dp ? pr + q.e + 1 : pr, rm, more);
            }

            return q;
        };
    }

    sub(x, y) {
        var d, e, i, j, k, len, pr, rm, xd, xe, xLTy, yd,
            x = this,
            Ctor = x.constructor;

        y = new Ctor(y);

        // If either is not finite...
        if (!x.d || !y.d) {

            // Return NaN if either is NaN.
            if (!x.s || !y.s) y = new Ctor(NaN);

            // Return y negated if x is finite and y is ±Infinity.
            else if (x.d) y.s = -y.s;

            // Return x if y is finite and x is ±Infinity.
            // Return x if both are ±Infinity with different signs.
            // Return NaN if both are ±Infinity with the same sign.
            else y = new Ctor(y.d || x.s !== y.s ? x : NaN);

            return y;
        }

        // If signs differ...
        if (x.s != y.s) {
            y.s = -y.s;
            return x.plus(y);
        }

        xd = x.d;
        yd = y.d;
        pr = Ctor.precision;
        rm = Ctor.rounding;

        // If either is zero...
        if (!xd[0] || !yd[0]) {

            // Return y negated if x is zero and y is non-zero.
            if (yd[0]) y.s = -y.s;

            // Return x if y is zero and x is non-zero.
            else if (xd[0]) y = new Ctor(x);

            // Return zero if both are zero.
            // From IEEE 754 (2008) 6.3: 0 - 0 = -0 - -0 = -0 when rounding to -Infinity.
            else return new Ctor(rm === 3 ? -0 : 0);

            return external ? finalise(y, pr, rm) : y;
        }

        // x and y are finite, non-zero numbers with the same sign.

        // Calculate base 1e7 exponents.
        e = mathfloor(y.e / LOG_BASE);
        xe = mathfloor(x.e / LOG_BASE);

        xd = xd.slice();
        k = xe - e;

        // If base 1e7 exponents differ...
        if (k) {
            xLTy = k < 0;

            if (xLTy) {
                d = xd;
                k = -k;
                len = yd.length;
            } else {
                d = yd;
                e = xe;
                len = xd.length;
            }

            // Numbers with massively different exponents would result in a very high number of
            // zeros needing to be prepended, but this can be avoided while still ensuring correct
            // rounding by limiting the number of zeros to `Math.ceil(pr / LOG_BASE) + 2`.
            i = Math.max(Math.ceil(pr / LOG_BASE), len) + 2;

            if (k > i) {
                k = i;
                d.length = 1;
            }

            // Prepend zeros to equalise exponents.
            d.reverse();
            for (i = k; i--;) d.push(0);
            d.reverse();

            // Base 1e7 exponents equal.
        } else {

            // Check digits to determine which is the bigger number.

            i = xd.length;
            len = yd.length;
            xLTy = i < len;
            if (xLTy) len = i;

            for (i = 0; i < len; i++) {
                if (xd[i] != yd[i]) {
                    xLTy = xd[i] < yd[i];
                    break;
                }
            }

            k = 0;
        }

        if (xLTy) {
            d = xd;
            xd = yd;
            yd = d;
            y.s = -y.s;
        }

        len = xd.length;

        // Append zeros to `xd` if shorter.
        // Don't add zeros to `yd` if shorter as subtraction only needs to start at `yd` length.
        for (i = yd.length - len; i > 0; --i) xd[len++] = 0;

        // Subtract yd from xd.
        for (i = yd.length; i > k;) {

            if (xd[--i] < yd[i]) {
                for (j = i; j && xd[--j] === 0;) xd[j] = BASE - 1;
                --xd[j];
                xd[i] += BASE;
            }

            xd[i] -= yd[i];
        }

        // Remove trailing zeros.
        for (; xd[--len] === 0;) xd.pop();

        // Remove leading zeros and adjust exponent accordingly.
        for (; xd[0] === 0; xd.shift()) --e;

        // Zero?
        if (!xd[0]) return new Ctor(rm === 3 ? -0 : 0);

        y.d = xd;
        y.e = getBase10Exponent(xd, e);

        return external ? finalise(y, pr, rm) : y;
    }

    add(x, y) {
        var carry, d, e, i, k, len, pr, rm, xd, yd,
            x = this,
            Ctor = x.constructor;

        y = new Ctor(y);

        // If either is not finite...
        if (!x.d || !y.d) {

            // Return NaN if either is NaN.
            if (!x.s || !y.s) y = new Ctor(NaN);

            // Return x if y is finite and x is ±Infinity.
            // Return x if both are ±Infinity with the same sign.
            // Return NaN if both are ±Infinity with different signs.
            // Return y if x is finite and y is ±Infinity.
            else if (!x.d) y = new Ctor(y.d || x.s === y.s ? x : NaN);

            return y;
        }

        // If signs differ...
        if (x.s != y.s) {
            y.s = -y.s;
            return x.minus(y);
        }

        xd = x.d;
        yd = y.d;
        pr = Ctor.precision;
        rm = Ctor.rounding;

        // If either is zero...
        if (!xd[0] || !yd[0]) {

            // Return x if y is zero.
            // Return y if y is non-zero.
            if (!yd[0]) y = new Ctor(x);

            return external ? finalise(y, pr, rm) : y;
        }

        // x and y are finite, non-zero numbers with the same sign.

        // Calculate base 1e7 exponents.
        k = mathfloor(x.e / LOG_BASE);
        e = mathfloor(y.e / LOG_BASE);

        xd = xd.slice();
        i = k - e;

        // If base 1e7 exponents differ...
        if (i) {

            if (i < 0) {
                d = xd;
                i = -i;
                len = yd.length;
            } else {
                d = yd;
                e = k;
                len = xd.length;
            }

            // Limit number of zeros prepended to max(ceil(pr / LOG_BASE), len) + 1.
            k = Math.ceil(pr / LOG_BASE);
            len = k > len ? k + 1 : len + 1;

            if (i > len) {
                i = len;
                d.length = 1;
            }

            // Prepend zeros to equalise exponents. Note: Faster to use reverse then do unshifts.
            d.reverse();
            for (; i--;) d.push(0);
            d.reverse();
        }

        len = xd.length;
        i = yd.length;

        // If yd is longer than xd, swap xd and yd so xd points to the longer array.
        if (len - i < 0) {
            i = len;
            d = yd;
            yd = xd;
            xd = d;
        }

        // Only start adding at yd.length - 1 as the further digits of xd can be left as they are.
        for (carry = 0; i;) {
            carry = (xd[--i] = xd[i] + yd[i] + carry) / BASE | 0;
            xd[i] %= BASE;
        }

        if (carry) {
            xd.unshift(carry);
            ++e;
        }

        // Remove trailing zeros.
        // No need to check for zero, as +x + +y != 0 && -x + -y != 0
        for (len = xd.length; xd[--len] == 0;) xd.pop();

        y.d = xd;
        y.e = getBase10Exponent(xd, e);

        return external ? finalise(y, pr, rm) : y;
    }
}

class Board {
    constructor(b){
        if (b === undefined) {
            this.record = {};
            return
        }
        this.record = b;
    }
    isAvailable(x, y) {
        return this.record[x + "," + y] === undefined
    }
    move(x, y, step) {
        this.record[x + "," + y] = step
    }
    color(x, y) { // 0 black; 1 white
        if (this.isAvailable(x,y)) {
            return 2
        }
        return this.record[x + "," + y] % 2
    }
}

class Utils {
    constructor(a, b) {
        this.a = a;
        this.b = b;
        this.count = 0;
        this.board = new Board();
        this.winner = null;
        this.hash = "";
        this.placeHolder = ""
    }

    isTurn(player) {
        return (this.count % 2 === 0 && player === this.a) ||
            (this.count % 2 === 1 && player === this.b)
    }

    move(player, x, y) {
        if (this.winner !== null) {
            return "this game has come to a close"
        }

        if (!this.isTurn(player)) {
            return "error player " + player + ", should be: " + (this.isTurn(this.a)? this.a:this.b)
        }
        if (!this.board.isAvailable(x, y)) {
            return "this cross has marked"
        }
        this.board.move(x, y, this.count ++);
        if (this._result(x, y)) {
            this.winner = player
        }
        return 0
    }

    _result(x, y) {
        return this._count(x, y, 1, 0) >= 5 ||
            this._count(x, y, 0, 1) >= 5 ||
            this._count(x, y, 1, 1) >= 5 ||
            this._count(x, y, 1, -1) >= 5;
    }

    _count(x, y, stepx, stepy) {
        let count = 1;
        const color = this.board.color(x,y);
        let cx = x;
        let cy = y;
        for (let i = 0; i < 4; i ++) {
            cx += stepx;
            cy += stepy;
            if (!Game._checkBound(cx) || !Game._checkBound(cy)) break;
            if (color !== this.board.color(cx, cy)) break;
            count++
        }
        cx = x;
        cy = y;
        for (let i = 0; i < 4; i ++) {
            cx -= stepx;
            cy -= stepy;
            if (color !== this.board.color(cx, cy)) break;
            count++
        }
        return count
    }

    static _checkBound(i) {
        return !(i < 0 || i >= 15);

    }

    static fromJSON(json) {
        const obj = JSON.parse(json);
        let g =  Object.assign(new Game, obj);
        g.board = Object.assign(new Board, obj.board);
        return g
    }
}


class PtfToken extends SafeMath, Utils {
    init () {
        blockchain.callWithAuth("token.iost", "create", [
            name,
            blockchain.contractName(),
            totalSupply,
            {
                fullName,
                decimal,
                canTransfer: true,
                onlyIssuerCanTransfer: true,
            }
        ]);
    }

    can_update (data) {
        return blockchain.requireAuth(blockchain.contractOwner(), 'active');
    }

    create_token () {
        if (!blockchain.requireAuth(blockchain.contractOwner(), 'active')) {
            return 'no permission';
        }

        blockchain.callWithAuth('token.iost', 'create', ['playg', blockchain.contractName(), 1000000, {'decimal': 8, 'canTransfer': true, 'fullName': 'PLAYGOLD'}]);
    }

    issue_token (amount) {
        if (!blockchain.requireAuth(blockchain.contractOwner(), 'active')) {
            return 'no permission';
        }

        blockchain.callWithAuth('token.iost', 'issue', ['playg', blockchain.contractOwner(), amount.toString()]);
    }

    withdraw (amount) {
        if (!blockchain.requireAuth(blockchain.contractOwner(), 'active')) {
            return 'no permission';
        }

        blockchain.withdraw(blockchain.contractOwner(), amount, 'Withdrawal from BlockDice');
        storage.put('last_balance', new Float64(storage.get('last_balance')).minus(amount).toFixed(8));
    }

    balance () {
        if (!blockchain.requireAuth(blockchain.contractOwner(), 'active')) {
            return 'no permission';
        }

        return blockchain.call('token.iost', 'balanceOf', ['iost', blockchain.contractName()]);
    }

    reset_leaderboard () {
        if (!blockchain.requireAuth('blockdicers', 'active')) {
            return 'no permission';
        }

        storage.put('website_profit', '0');

        let c = blockchain.contractName();
        let pool = new Float64(storage.get('leaderboard_pool'));
        let lb = JSON.parse(storage.get('leaderboard'));

        if (lb[2][1] != c) {
            let x = pool.div(7);
            blockchain.withdraw(lb[0][1], x.multi(4).toFixed(8), '1st Place in weekly BlockDice leaderboard!');
            blockchain.withdraw(lb[1][1], x.multi(2).toFixed(8), '2nd Place in weekly BlockDice leaderboard!');
            blockchain.withdraw(lb[2][1], x.toFixed(8), '3rd Place in weekly BlockDice leaderboard!');
        }
        else if (lb[1][1] != c) {
            let x = pool.div(3);
            blockchain.withdraw(lb[0][1], x.multi(2).toFixed(8), '1st Place in weekly BlockDice leaderboard!');
            blockchain.withdraw(lb[1][1], x.toFixed(8), '2nd Place in weekly BlockDice leaderboard!');
        }
        else if (lb[0][1] != c) {
            blockchain.withdraw(lb[0][1], pool.toFixed(8), '1st Place in weekly BlockDice leaderboard!');
        }

        storage.put('leaderboard_index', new Int64(storage.get('leaderboard_index')).plus(1).toString());
        storage.put('leaderboard_pool', '0');
        storage.put('leaderboard', JSON.stringify([['0', c], ['0', c], ['0', c], ['0', c], ['0', c], ['0', c], ['0', c], ['0', c], ['0', c], ['0', c]]));

        let last_balance = new Float64(storage.get('last_balance')).minus(pool);
        storage.put('last_balance', last_balance.toFixed(8));
    }

    stake (_amount) {
        if (!blockchain.requireAuth(tx.publisher, 'active')) {
            throw new Error('no active auth');
        }

        let amount = new Float64(_amount);

        if (amount.lt(0.01)) {
            throw new Error('amount should be >= 0.01');
        }

        blockchain.callWithAuth('token.iost', 'transfer', ['playg', tx.publisher, blockchain.contractName(), amount.toFixed(8), 'Staking ' + amount.toFixed(2) + ' PLAYG!']);

        let stakers = JSON.parse(storage.get('stakers_hold'));
        if (stakers.includes(tx.publisher)) {
            let staked = new Float64(storage.mapGet(tx.publisher, 'staked')).plus(amount).toFixed(8);
            storage.mapPut(tx.publisher, 'staked', staked);
        }
        else {
            stakers.push(tx.publisher);
            storage.put('stakers_hold', JSON.stringify(stakers));
            storage.mapPut(tx.publisher, 'staked', amount.toFixed(8));
            storage.mapPut(tx.publisher, 'divs', '0');
        }

        let total_staked = new Float64(storage.get('total_staked')).plus(amount).toFixed(8);
        storage.put('total_staked', total_staked);
    }

    unstake (_amount) {
        if (!blockchain.requireAuth(tx.publisher, 'active')) {
            throw new Error('no active auth');
        }

        let amount = new Float64(_amount);

        if (amount.lt(0.01)) {
            throw new Error('amount should be >= 0.01');
        }

        let staked = new Float64(storage.mapGet(tx.publisher, 'staked')).minus(amount);
        if (staked.lt(0)) {
            throw new Error('not enough PLAYG staked');
        }

        let divs = new Float64(storage.mapGet(tx.publisher, 'divs'));

        if (staked.lte(0) && divs.lte(0)) {
            storage.mapDel(tx.publisher, 'staked');
            storage.mapDel(tx.publisher, 'divs');
            let stakers = JSON.parse(storage.get('stakers_hold'));
            let index = stakers.indexOf(tx.publisher);
            if (index != -1) {
                stakers.splice(index, 1);
            }
            storage.put('stakers_hold', JSON.stringify(stakers));
        }
        else {
            storage.mapPut(tx.publisher, 'staked', staked.toFixed(8));
        }

        let total_staked = new Float64(storage.get('total_staked')).minus(amount);
        storage.put('total_staked', total_staked.toFixed(8));

        blockchain.callWithAuth('token.iost', 'transfer', ['playg', blockchain.contractName(), tx.publisher, amount.toFixed(2), 'Unstaking ' + amount + ' PLAYG!'])
    }

    claim () {
        if (!blockchain.requireAuth(tx.publisher, 'active')) {
            throw new Error('no active auth');
        }

        let staked = new Float64(storage.mapGet(tx.publisher, 'staked'));
        let divs = new Float64(storage.mapGet(tx.publisher, 'divs'));

        if (staked.lte(0) && divs.lte(0)) {
            storage.mapDel(tx.publisher, 'staked');
            storage.mapDel(tx.publisher, 'divs');
            let stakers = JSON.parse(storage.get('stakers_hold'));
            let index = stakers.indexOf(tx.publisher);
            if (index != -1) {
                stakers.splice(index, 1);
            }
            storage.put('stakers_hold', JSON.stringify(stakers));
        }
        else {
            storage.mapPut(tx.publisher, 'divs', '0');
        }

        blockchain.withdraw(tx.publisher, divs.toFixed(8), 'Divs from BlockDice');

        let last_balance = new Float64(storage.get('last_balance')).minus(divs);
        storage.put('last_balance', last_balance.toFixed(8));
    }

    test () {
        if (!blockchain.requireAuth('blockdicers', 'active')) {
            return 'no permission';
        }

        let stakers = JSON.parse(storage.get('stakers_hold'));
        let total_divs = new Float64('0');
        for (let i = 0; i < stakers.length; i += 1) {
            total_divs = total_divs.plus(storage.mapGet(stakers[i], 'divs'));
        }

        storage.put('unclaimed_divs', total_divs.toFixed(8));

        return [total_divs, storage.get('website_profit'), storage.get('last_balance'), blockchain.call('token.iost', 'balanceOf', ['iost', blockchain.contractName()]), storage.get('total_staked'), storage.get('average_k'), storage.get('leaderboard_pool'), storage.get('jackpot'), storage.mapLen('bets_to_resolve'), storage.get('jackpot_winner')];
    }


    dice (_chance, _hilo, _amount) {
        if (!blockchain.requireAuth(tx.publisher, 'active')) {
            throw new Error('no active auth');
        }

        blockchain.deposit(tx.publisher, _amount, 'Bet on BlockDice');

        storage.mapPut('bets_to_resolve', tx.hash, JSON.stringify([tx.publisher, _chance, _hilo, _amount]));
    }

    resolve_bet (txhash) {
        if (!blockchain.requireAuth('blockdicers', 'active')) {
            throw new Error('no permission');
        }

        let ret = JSON.parse(storage.mapGet('bets_to_resolve', txhash));

        if (ret == null) {
            throw new Error('bet not found');
        }

        storage.mapDel('bets_to_resolve', txhash);

        let txpublisher = ret[0];
        let _chance = ret[1];
        let _hilo = ret[2];
        let _amount = ret[3];

        if (_chance > 95 || _chance < 1) {
            blockchain.withdraw(txpublisher, _amount, 'Refund bet from BlockDice');
            return 'chance should be >= 1 and <= 95';
        }
        if (_hilo != 0 && _hilo != 1) {
            blockchain.withdraw(txpublisher, _amount, 'Refund bet from BlockDice');
            return 'hilo should be 0 and 1';
        }
        if (new Float64(_amount).lt(1)) {
            blockchain.withdraw(txpublisher, _amount, 'Refund bet from BlockDice');
            return 'amount should be >= 1';
        }

        let chance = new Int64(_chance);
        let amount = new Float64(_amount);

        let limit = new Float64(0.00187269).minus(new Float64(0.00037689).multi(Math.log(chance)));

        let multiplier = new Float64('100.00').div(chance);
        let count_multi = multiplier.multi(0.985);
        let reward = amount.multi(count_multi);

        let bankroll = new Float64(blockchain.call('token.iost', 'balanceOf', ['iost', blockchain.contractName()]));

        if (reward.minus(amount).gt(bankroll.multi(limit))) {
            blockchain.withdraw(txpublisher, _amount, 'Refund bet from BlockDice');
            return 'bet profit is too much';
        }

        let hash = IOSTCrypto.sha3(tx.hash + block.parent_hash + storage.get('rndh'));
        storage.put('rndh', hash);

        let jackpot_winner = false;
        if (hash[5] == 'R' && hash[15] == 'D' && hash[25] == 'e') {
            if (['1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B'].includes(hash[35])) {
                jackpot_winner = true;
            }
        }

        let sum = new Int64(0);
        for (let i = 0; i < hash.length; i++) {
            sum = sum.plus(hash.charCodeAt(i));
        }
        let roll = sum.mod(100).plus(1);

        // Weekly lb

        let leaderboard = JSON.parse(storage.get('leaderboard'));

        let lb_index = storage.get('leaderboard_index');
        let lb_index_p = storage.mapGet(txpublisher, 'lb_index')

        if (lb_index_p != lb_index) {
            storage.mapPut(txpublisher, 'wager', '0');
            storage.mapPut(txpublisher, 'lb_index', lb_index);
        }

        let wager;

        if (storage.mapHas(txpublisher, 'wager')) {
            wager = new Float64(storage.mapGet(txpublisher, 'wager')).plus(amount);
            storage.mapPut(txpublisher, 'wager', wager.toFixed(8));
        }
        else {
            wager = new Float64(amount);
            storage.mapPut(txpublisher, 'wager', wager.toFixed(8));
        }

        let in_leads = 9;

        for (let i = 0; i < 10; i += 1) {
            if (leaderboard[i][1] == txpublisher) {
                in_leads = i;
                break;
            }
        }

        for (let i = in_leads; i >= 0; i -= 1) {
            let leader = leaderboard[i];
            if (wager.gte(leader[0])) {
                if (leader[1] == txpublisher) {
                    leaderboard[i][0] = wager.toFixed(8);
                }
                else if (i < 9) {
                    let leader2 = leaderboard[i + 1];
                    leaderboard[i] = leader2;
                    leaderboard[i + 1] = leader;
                }
                else {
                    leaderboard[i] = [wager.toFixed(8), txpublisher];
                }
            }
            else {
                break;
            }
        }

        storage.put('leaderboard', JSON.stringify(leaderboard));

        storage.put('website_profit', new Float64(storage.get('website_profit')).plus(amount).toFixed(8));

        if (jackpot_winner || (_hilo == 0 && roll.lte(chance)) || (_hilo == 1 && roll.gt(new Float64(100).minus(chance)))) {
            let average_k = new Float64(storage.get('average_k'));
            if (!jackpot_winner && bankroll.minus(reward.minus(amount)).lt(new Float64(storage.get('last_balance')).multi(average_k))) {
                if (average_k.lt(0.99)) {
                    storage.put('average_k', '0.992');
                    storage.put('last_balance', bankroll.plus(amount).toFixed(8));
                }

                if (_hilo == 0) {
                    roll = new Int64(new Int64(sum.mod(new Int64(100).minus(chance))).plus(chance).plus(1));
                }
                else {
                    roll = new Int64(new Int64(sum.mod(new Int64(100).minus(chance))).plus(1));
                }

                if (bankroll.plus(amount).gt(new Float64(storage.get('last_balance')))) {
                    storage.put('last_balance', bankroll.plus(amount).toFixed(8));
                }

                blockchain.receipt('Rolled: ' + roll.toString());
            }

            else {
                if (jackpot_winner) {
                    blockchain.receipt('Rolled: 777');
                    blockchain.withdraw(txpublisher, storage.get('jackpot'), 'JACKPOT WINNER ON BLOCKDICE.APP');
                    storage.put('last_balance', new Float64(storage.get('last_balance')).minus(storage.get('jackpot')).toFixed(8));
                    storage.put('jackpot', '1000');
                    storage.put('jackpot_winner', txpublisher);
                }
                else {
                    blockchain.receipt('Rolled: ' + roll.toString());
                    blockchain.withdraw(txpublisher, reward.toFixed(8), 'Win from BlockDice\nRolled: ' + roll.toString());
                }

                storage.put('website_profit', new Float64(storage.get('website_profit')).minus(reward).toFixed(8));

                let total_staked = new Float64(storage.get('total_staked'));
                let stakers = JSON.parse(storage.get('stakers_hold'));
                let little_part = multiplier.multi(0.001).multi(amount);
                let divs_profit = little_part.multi(5);
                let leaderboard_pool_inc = little_part.multi(5);

                storage.put('jackpot', new Float64(storage.get('jackpot')).plus(little_part.multi(0.1)).toFixed(8));

                storage.put('leaderboard_pool', new Float64(storage.get('leaderboard_pool')).plus(leaderboard_pool_inc).toFixed(8));

                for (let i = 0; i < stakers.length; i += 1) {
                    if (total_staked.gt(0)) {
                        let staker = stakers[i];
                        let hold = new Float64(storage.mapGet(staker, 'staked'));
                        let part = hold.div(total_staked);
                        let profit = part.multi(divs_profit);
                        let divs = new Float64(storage.mapGet(staker, 'divs')).plus(profit);
                        storage.mapPut(staker, 'divs', divs.toFixed(8));
                    }
                }
            }
        }

        else {
            blockchain.receipt('Rolled: ' + roll.toString());

            if (bankroll.plus(amount).gt(new Float64(storage.get('last_balance')))) {
                storage.put('last_balance', bankroll.plus(amount).toFixed(8));
            }
        }

        let mining_rate = new Int64(storage.get('mining_rate'));
        let play_reward = amount.div(mining_rate);

        let mined_round = new Float64(storage.get('mined_round'));
        if (mined_round.plus(play_reward).gt(200000)) {
            mined_round = mined_round.plus(play_reward).minus(200000);
            storage.put('mined_round', mined_round.toFixed(8));
            let current_round = new Int64(storage.get('current_round'));
            let new_round = current_round.plus(1);
            storage.put('current_round', new_round.toString());
            storage.put('mining_rate', mining_rate.plus(50).toString());
        }
        else {
            mined_round = mined_round.plus(play_reward);
            storage.put('mined_round', mined_round.toFixed(8));
        }

        blockchain.callWithAuth('token.iost', 'issue', ['playg', txpublisher, play_reward.toFixed(8)]);
    }

    //return Int64(seq + 1)
    _withdrawSequence() {

        let nowSeq = storage.get(WITHDRAW_SEQ_KEY);
        let nextSeq = new Int64(nowSeq).plus(1);

        storage.put(WITHDRAW_SEQ_KEY, nextSeq.toString());
        return nextSeq;
    }

    //return secconds.
    _nowTimeSec() {
        return new BigNumber(block.time).div(1000000000).toNumber().toFixed(0);
    }

    //irc -> erc 출금.
    swapWithdraw(amountStr, ercAccount) {

        //swap용 토큰 예치.
        blockchain.callWithAuth("token.iost", "transfer", [TOKEN_NAME, tx.publisher, blockchain.contractName(), amountStr, "swapWithdraw"]);

        //status: 0:request, 1:inProcess: 2:done
        let oneData = {account:tx.publisher, amount:amountStr, ercAccount:ercAccount, requestTime:this._nowTimeSec(), status:'0'};

        let withdrawSeq = this._withdrawSequence();
        storage.mapPut(WITHDRAW_MAPKEY, withdrawSeq.toString(), JSON.stringify(oneData));
    }

    //for admin : swap progress update
    updateStatus(withdrawSeqStr, statusStr) {

        //admin일때만 처리.
        if (tx.publisher === blockchain.contractOwner()) {

            //혹시나 없는지 check
            if (!storage.mapHas(WITHDRAW_MAPKEY, withdrawSeqStr)) {
                throw new Error("updateStatus No Data Error" + tx.publisher + " (withdrawSeq, status)-" + withdrawSeqStr + "," +  statusStr);
            }

            //data 처리
            let oneData = JSON.parse(storage.mapGet(WITHDRAW_MAPKEY, withdrawSeqStr));
            oneData.status = statusStr;

            storage.mapPut(WITHDRAW_MAPKEY, withdrawSeqStr, JSON.stringify(oneData));

        }else {
            throw new Error("updateStatus Authority Error:" + tx.publisher + " (withdrawSeq, status)-" + withdrawSeqStr + "," +  statusStr);
        }
    }
}

module.exports = PtfToken;