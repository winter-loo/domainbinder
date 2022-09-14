navigator = {
	"appCodeName": "Mozilla",
	"appName": "Netscape",
	"appVersion": "5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/105.0.0.0 Safari/537.36"
}

function setTimeout(fn, t) {
	fn()
}

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary & 0xffffff) == 0xefcafe);

// (public) Constructor
function BigInteger(a, b, c) {
	if (a != null)
		if ("number" == typeof a) this.fromNumber(a, b, c);
		else if (b == null && "string" != typeof a) this.fromString(a, 256);
		else this.fromString(a, b);
}

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i, x, w, j, c, n) {
	while (--n >= 0) {
		var v = x * this[i++] + w[j] + c;
		c = Math.floor(v / 0x4000000);
		w[j++] = v & 0x3ffffff;
	}
	return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i, x, w, j, c, n) {
	var xl = x & 0x7fff, xh = x >> 15;
	while (--n >= 0) {
		var l = this[i] & 0x7fff;
		var h = this[i++] >> 15;
		var m = xh * l + h * xl;
		l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
		c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
		w[j++] = l & 0x3fffffff;
	}
	return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i, x, w, j, c, n) {
	var xl = x & 0x3fff, xh = x >> 14;
	while (--n >= 0) {
		var l = this[i] & 0x3fff;
		var h = this[i++] >> 14;
		var m = xh * l + h * xl;
		l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
		c = (l >> 28) + (m >> 14) + xh * h;
		w[j++] = l & 0xfffffff;
	}
	return c;
}
if (j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
	BigInteger.prototype.am = am2;
	dbits = 30;
}
else if (j_lm && (navigator.appName != "Netscape")) {
	BigInteger.prototype.am = am1;
	dbits = 26;
}
else { // Mozilla/Netscape seems to prefer am3
	BigInteger.prototype.am = am3;
	dbits = 28;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1 << dbits) - 1);
BigInteger.prototype.DV = (1 << dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2, BI_FP);
BigInteger.prototype.F1 = BI_FP - dbits;
BigInteger.prototype.F2 = 2 * dbits - BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr, vv;
rr = "0".charCodeAt(0);
for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s, i) {
	var c = BI_RC[s.charCodeAt(i)];
	return (c == null) ? -1 : c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
	for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
	r.t = this.t;
	r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
	this.t = 1;
	this.s = (x < 0) ? -1 : 0;
	if (x > 0) this[0] = x;
	else if (x < -1) this[0] = x + this.DV;
	else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s, b) {
	var k;
	if (b == 16) k = 4;
	else if (b == 8) k = 3;
	else if (b == 256) k = 8; // byte array
	else if (b == 2) k = 1;
	else if (b == 32) k = 5;
	else if (b == 4) k = 2;
	else { this.fromRadix(s, b); return; }
	this.t = 0;
	this.s = 0;
	var i = s.length, mi = false, sh = 0;
	while (--i >= 0) {
		var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
		if (x < 0) {
			if (s.charAt(i) == "-") mi = true;
			continue;
		}
		mi = false;
		if (sh == 0)
			this[this.t++] = x;
		else if (sh + k > this.DB) {
			this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh;
			this[this.t++] = (x >> (this.DB - sh));
		}
		else
			this[this.t - 1] |= x << sh;
		sh += k;
		if (sh >= this.DB) sh -= this.DB;
	}
	if (k == 8 && (s[0] & 0x80) != 0) {
		this.s = -1;
		if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh;
	}
	this.clamp();
	if (mi) BigInteger.ZERO.subTo(this, this);
}

// (protected) clamp off excess high words
function bnpClamp() {
	var c = this.s & this.DM;
	while (this.t > 0 && this[this.t - 1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
	if (this.s < 0) return "-" + this.negate().toString(b);
	var k;
	if (b == 16) k = 4;
	else if (b == 8) k = 3;
	else if (b == 2) k = 1;
	else if (b == 32) k = 5;
	else if (b == 4) k = 2;
	else return this.toRadix(b);
	var km = (1 << k) - 1, d, m = false, r = "", i = this.t;
	var p = this.DB - (i * this.DB) % k;
	if (i-- > 0) {
		if (p < this.DB && (d = this[i] >> p) > 0) { m = true; r = int2char(d); }
		while (i >= 0) {
			if (p < k) {
				d = (this[i] & ((1 << p) - 1)) << (k - p);
				d |= this[--i] >> (p += this.DB - k);
			}
			else {
				d = (this[i] >> (p -= k)) & km;
				if (p <= 0) { p += this.DB; --i; }
			}
			if (d > 0) m = true;
			if (m) r += int2char(d);
		}
	}
	return m ? r : "0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this, r); return r; }

// (public) |this|
function bnAbs() { return (this.s < 0) ? this.negate() : this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
	var r = this.s - a.s;
	if (r != 0) return r;
	var i = this.t;
	r = i - a.t;
	if (r != 0) return (this.s < 0) ? -r : r;
	while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r;
	return 0;
}

// returns bit length of the integer x
function nbits(x) {
	var r = 1, t;
	if ((t = x >>> 16) != 0) { x = t; r += 16; }
	if ((t = x >> 8) != 0) { x = t; r += 8; }
	if ((t = x >> 4) != 0) { x = t; r += 4; }
	if ((t = x >> 2) != 0) { x = t; r += 2; }
	if ((t = x >> 1) != 0) { x = t; r += 1; }
	return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
	if (this.t <= 0) return 0;
	return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n, r) {
	var i;
	for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
	for (i = n - 1; i >= 0; --i) r[i] = 0;
	r.t = this.t + n;
	r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n, r) {
	for (var i = n; i < this.t; ++i) r[i - n] = this[i];
	r.t = Math.max(this.t - n, 0);
	r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n, r) {
	var bs = n % this.DB;
	var cbs = this.DB - bs;
	var bm = (1 << cbs) - 1;
	var ds = Math.floor(n / this.DB), c = (this.s << bs) & this.DM, i;
	for (i = this.t - 1; i >= 0; --i) {
		r[i + ds + 1] = (this[i] >> cbs) | c;
		c = (this[i] & bm) << bs;
	}
	for (i = ds - 1; i >= 0; --i) r[i] = 0;
	r[ds] = c;
	r.t = this.t + ds + 1;
	r.s = this.s;
	r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n, r) {
	r.s = this.s;
	var ds = Math.floor(n / this.DB);
	if (ds >= this.t) { r.t = 0; return; }
	var bs = n % this.DB;
	var cbs = this.DB - bs;
	var bm = (1 << bs) - 1;
	r[0] = this[ds] >> bs;
	for (var i = ds + 1; i < this.t; ++i) {
		r[i - ds - 1] |= (this[i] & bm) << cbs;
		r[i - ds] = this[i] >> bs;
	}
	if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
	r.t = this.t - ds;
	r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a, r) {
	var i = 0, c = 0, m = Math.min(a.t, this.t);
	while (i < m) {
		c += this[i] - a[i];
		r[i++] = c & this.DM;
		c >>= this.DB;
	}
	if (a.t < this.t) {
		c -= a.s;
		while (i < this.t) {
			c += this[i];
			r[i++] = c & this.DM;
			c >>= this.DB;
		}
		c += this.s;
	}
	else {
		c += this.s;
		while (i < a.t) {
			c -= a[i];
			r[i++] = c & this.DM;
			c >>= this.DB;
		}
		c -= a.s;
	}
	r.s = (c < 0) ? -1 : 0;
	if (c < -1) r[i++] = this.DV + c;
	else if (c > 0) r[i++] = c;
	r.t = i;
	r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a, r) {
	var x = this.abs(), y = a.abs();
	var i = x.t;
	r.t = i + y.t;
	while (--i >= 0) r[i] = 0;
	for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
	r.s = 0;
	r.clamp();
	if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
	var x = this.abs();
	var i = r.t = 2 * x.t;
	while (--i >= 0) r[i] = 0;
	for (i = 0; i < x.t - 1; ++i) {
		var c = x.am(i, x[i], r, 2 * i, 0, 1);
		if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
			r[i + x.t] -= x.DV;
			r[i + x.t + 1] = 1;
		}
	}
	if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
	r.s = 0;
	r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m, q, r) {
	var pm = m.abs();
	if (pm.t <= 0) return;
	var pt = this.abs();
	if (pt.t < pm.t) {
		if (q != null) q.fromInt(0);
		if (r != null) this.copyTo(r);
		return;
	}
	if (r == null) r = nbi();
	var y = nbi(), ts = this.s, ms = m.s;
	var nsh = this.DB - nbits(pm[pm.t - 1]);	// normalize modulus
	if (nsh > 0) { pm.lShiftTo(nsh, y); pt.lShiftTo(nsh, r); }
	else { pm.copyTo(y); pt.copyTo(r); }
	var ys = y.t;
	var y0 = y[ys - 1];
	if (y0 == 0) return;
	var yt = y0 * (1 << this.F1) + ((ys > 1) ? y[ys - 2] >> this.F2 : 0);
	var d1 = this.FV / yt, d2 = (1 << this.F1) / yt, e = 1 << this.F2;
	var i = r.t, j = i - ys, t = (q == null) ? nbi() : q;
	y.dlShiftTo(j, t);
	if (r.compareTo(t) >= 0) {
		r[r.t++] = 1;
		r.subTo(t, r);
	}
	BigInteger.ONE.dlShiftTo(ys, t);
	t.subTo(y, y);	// "negative" y so we can replace sub with am later
	while (y.t < ys) y[y.t++] = 0;
	while (--j >= 0) {
		// Estimate quotient digit
		var qd = (r[--i] == y0) ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
		if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {	// Try it out
			y.dlShiftTo(j, t);
			r.subTo(t, r);
			while (r[i] < --qd) r.subTo(t, r);
		}
	}
	if (q != null) {
		r.drShiftTo(ys, q);
		if (ts != ms) BigInteger.ZERO.subTo(q, q);
	}
	r.t = ys;
	r.clamp();
	if (nsh > 0) r.rShiftTo(nsh, r);	// Denormalize remainder
	if (ts < 0) BigInteger.ZERO.subTo(r, r);
}

// (public) this mod a
function bnMod(a) {
	var r = nbi();
	this.abs().divRemTo(a, null, r);
	if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
	return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
	if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
	else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m, null, x); }
function cMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }
function cSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
	if (this.t < 1) return 0;
	var x = this[0];
	if ((x & 1) == 0) return 0;
	var y = x & 3;		// y == 1/x mod 2^2
	y = (y * (2 - (x & 0xf) * y)) & 0xf;	// y == 1/x mod 2^4
	y = (y * (2 - (x & 0xff) * y)) & 0xff;	// y == 1/x mod 2^8
	y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff;	// y == 1/x mod 2^16
	// last step - calculate inverse mod DV directly;
	// assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
	y = (y * (2 - x * y % this.DV)) % this.DV;		// y == 1/x mod 2^dbits
	// we really want the negative inverse, and -DV < y < DV
	return (y > 0) ? this.DV - y : -y;
}

// Montgomery reduction
function Montgomery(m) {
	this.m = m;
	this.mp = m.invDigit();
	this.mpl = this.mp & 0x7fff;
	this.mph = this.mp >> 15;
	this.um = (1 << (m.DB - 15)) - 1;
	this.mt2 = 2 * m.t;
}

// xR mod m
function montConvert(x) {
	var r = nbi();
	x.abs().dlShiftTo(this.m.t, r);
	r.divRemTo(this.m, null, r);
	if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
	return r;
}

// x/R mod m
function montRevert(x) {
	var r = nbi();
	x.copyTo(r);
	this.reduce(r);
	return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
	while (x.t <= this.mt2)	// pad x so am has enough room later
		x[x.t++] = 0;
	for (var i = 0; i < this.m.t; ++i) {
		// faster way of calculating u0 = x[i]*mp mod DV
		var j = x[i] & 0x7fff;
		var u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM;
		// use am to combine the multiply-shift-add into one call
		j = i + this.m.t;
		x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
		// propagate carry
		while (x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
	}
	x.clamp();
	x.drShiftTo(this.m.t, x);
	if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t > 0) ? (this[0] & 1) : this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e, z) {
	if (e > 0xffffffff || e < 1) return BigInteger.ONE;
	var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e) - 1;
	g.copyTo(r);
	while (--i >= 0) {
		z.sqrTo(r, r2);
		if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
		else { var t = r; r = r2; r2 = t; }
	}
	return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e, m) {
	var z;
	if (e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
	return this.exp(e, z);
}

// protected
BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp;

// public
BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt;

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// prng4.js - uses Arcfour as a PRNG

function Arcfour() {
	this.i = 0;
	this.j = 0;
	this.S = new Array();
}

// Initialize arcfour context from key, an array of ints, each from [0..255]
function ARC4init(key) {
	var i, j, t;
	for (i = 0; i < 256; ++i)
		this.S[i] = i;
	j = 0;
	for (i = 0; i < 256; ++i) {
		j = (j + this.S[i] + key[i % key.length]) & 255;
		t = this.S[i];
		this.S[i] = this.S[j];
		this.S[j] = t;
	}
	this.i = 0;
	this.j = 0;
}

function ARC4next() {
	var t;
	this.i = (this.i + 1) & 255;
	this.j = (this.j + this.S[this.i]) & 255;
	t = this.S[this.i];
	this.S[this.i] = this.S[this.j];
	this.S[this.j] = t;
	return this.S[(t + this.S[this.i]) & 255];
}

Arcfour.prototype.init = ARC4init;
Arcfour.prototype.next = ARC4next;

// Plug in your RNG constructor here
function prng_newstate() {
	return new Arcfour();
}

// Pool size must be a multiple of 4 and greater than 32.
// An array of bytes the size of the pool will be passed to init()
var rng_psize = 256;

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Random number generator - requires a PRNG backend, e.g. prng4.js

// For best results, put code like
// <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
// in your main HTML document.

var rng_state;
var rng_pool;
var rng_pptr;

// Mix in a 32-bit integer into the pool
function rng_seed_int(x) {
	rng_pool[rng_pptr++] ^= x & 255;
	rng_pool[rng_pptr++] ^= (x >> 8) & 255;
	rng_pool[rng_pptr++] ^= (x >> 16) & 255;
	rng_pool[rng_pptr++] ^= (x >> 24) & 255;
	if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
}

// Mix in the current time (w/milliseconds) into the pool
function rng_seed_time() {
	rng_seed_int(new Date().getTime());
}

// Initialize the pool with junk if needed.
if (rng_pool == null) {
	rng_pool = new Array();
	rng_pptr = 0;
	var t;
	if (window !== undefined &&
		(window.crypto !== undefined ||
			window.msCrypto !== undefined)) {
		var crypto = window.crypto || window.msCrypto;
		if (crypto.getRandomValues) {
			// Use webcrypto if available
			var ua = new Uint8Array(32);
			crypto.getRandomValues(ua);
			for (t = 0; t < 32; ++t)
				rng_pool[rng_pptr++] = ua[t];
		} else if (navigator.appName == "Netscape" && navigator.appVersion < "5") {
			// Extract entropy (256 bits) from NS4 RNG if available
			var z = window.crypto.random(32);
			for (t = 0; t < z.length; ++t)
				rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
		}
	}
	while (rng_pptr < rng_psize) {  // extract some randomness from Math.random()
		t = Math.floor(65536 * Math.random());
		rng_pool[rng_pptr++] = t >>> 8;
		rng_pool[rng_pptr++] = t & 255;
	}
	rng_pptr = 0;
	rng_seed_time();
	//rng_seed_int(window.screenX);
	//rng_seed_int(window.screenY);
}

function rng_get_byte() {
	if (rng_state == null) {
		rng_seed_time();
		rng_state = prng_newstate();
		rng_state.init(rng_pool);
		for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
			rng_pool[rng_pptr] = 0;
		rng_pptr = 0;
		//rng_pool = null;
	}
	// TODO: allow reseeding after first request
	return rng_state.next();
}

function rng_get_bytes(ba) {
	var i;
	for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
}

function SecureRandom() { }

SecureRandom.prototype.nextBytes = rng_get_bytes;

/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
// Depends on jsbn.js and rng.js

// Version 1.1: support utf-8 encoding in pkcs1pad2

// convert a (hex) string to a bignum object
function parseBigInt(str, r) {
	return new BigInteger(str, r);
}

function linebrk(s, n) {
	var ret = "";
	var i = 0;
	while (i + n < s.length) {
		ret += s.substring(i, i + n) + "\n";
		i += n;
	}
	return ret + s.substring(i, s.length);
}

function byte2Hex(b) {
	if (b < 0x10)
		return "0" + b.toString(16);
	else
		return b.toString(16);
}

// PKCS#1 (type 2, random) pad input string s to n bytes, and return a bigint
function pkcs1pad2(s, n) {
	if (n < s.length + 11) { // TODO: fix for utf-8
		throw "Message too long for RSA";
		return null;
	}
	var ba = new Array();
	var i = s.length - 1;
	while (i >= 0 && n > 0) {
		var c = s.charCodeAt(i--);
		if (c < 128) { // encode using utf-8
			ba[--n] = c;
		}
		else if ((c > 127) && (c < 2048)) {
			ba[--n] = (c & 63) | 128;
			ba[--n] = (c >> 6) | 192;
		}
		else {
			ba[--n] = (c & 63) | 128;
			ba[--n] = ((c >> 6) & 63) | 128;
			ba[--n] = (c >> 12) | 224;
		}
	}
	ba[--n] = 0;
	var rng = new SecureRandom();
	var x = new Array();
	while (n > 2) { // random non-zero pad
		x[0] = 0;
		while (x[0] == 0) rng.nextBytes(x);
		ba[--n] = x[0];
	}
	ba[--n] = 2;
	ba[--n] = 0;
	return new BigInteger(ba);
}

// PKCS#1 (OAEP) mask generation function
function oaep_mgf1_arr(seed, len, hash) {
	var mask = '', i = 0;

	while (mask.length < len) {
		mask += hash(String.fromCharCode.apply(String, seed.concat([
			(i & 0xff000000) >> 24,
			(i & 0x00ff0000) >> 16,
			(i & 0x0000ff00) >> 8,
			i & 0x000000ff])));
		i += 1;
	}

	return mask;
}

/**
 * PKCS#1 (OAEP) pad input string s to n bytes, and return a bigint
 * @name oaep_pad
 * @param s raw string of message
 * @param n key length of RSA key
 * @param hash JavaScript function to calculate raw hash value from raw string or algorithm name (ex. "SHA1") 
 * @param hashLen byte length of resulted hash value (ex. 20 for SHA1)
 * @return {BigInteger} BigInteger object of resulted PKCS#1 OAEP padded message
 * @description
 * This function calculates OAEP padded message from original message.<br/>
 * NOTE: Since jsrsasign 6.2.0, 'hash' argument can accept an algorithm name such as "sha1".
 * @example
 * oaep_pad("aaa", 128) &rarr; big integer object // SHA-1 by default
 * oaep_pad("aaa", 128, function(s) {...}, 20);
 * oaep_pad("aaa", 128, "sha1");
 */
function oaep_pad(s, n, hash, hashLen) {
	var MD = KJUR.crypto.MessageDigest;
	var Util = KJUR.crypto.Util;
	var algName = null;

	if (!hash) hash = "sha1";

	if (typeof hash === "string") {
		algName = MD.getCanonicalAlgName(hash);
		hashLen = MD.getHashLength(algName);
		hash = function (s) {
			return hextorstr(Util.hashHex(rstrtohex(s), algName));
		};
	}

	if (s.length + 2 * hashLen + 2 > n) {
		throw "Message too long for RSA";
	}

	var PS = '', i;

	for (i = 0; i < n - s.length - 2 * hashLen - 2; i += 1) {
		PS += '\x00';
	}

	var DB = hash('') + PS + '\x01' + s;
	var seed = new Array(hashLen);
	new SecureRandom().nextBytes(seed);

	var dbMask = oaep_mgf1_arr(seed, DB.length, hash);
	var maskedDB = [];

	for (i = 0; i < DB.length; i += 1) {
		maskedDB[i] = DB.charCodeAt(i) ^ dbMask.charCodeAt(i);
	}

	var seedMask = oaep_mgf1_arr(maskedDB, seed.length, hash);
	var maskedSeed = [0];

	for (i = 0; i < seed.length; i += 1) {
		maskedSeed[i + 1] = seed[i] ^ seedMask.charCodeAt(i);
	}

	return new BigInteger(maskedSeed.concat(maskedDB));
}

// "empty" RSA key constructor
function RSAKey() {
	this.n = null;
	this.e = 0;
	this.d = null;
	this.p = null;
	this.q = null;
	this.dmp1 = null;
	this.dmq1 = null;
	this.coeff = null;
}

// Set the public key fields N and e from hex strings
function RSASetPublic(N, E) {
	this.isPublic = true;
	this.isPrivate = false;
	if (typeof N !== "string") {
		this.n = N;
		this.e = E;
	} else if (N != null && E != null && N.length > 0 && E.length > 0) {
		this.n = parseBigInt(N, 16);
		this.e = parseInt(E, 16);
	} else {
		throw "Invalid RSA public key";
	}
}

// Perform raw public operation on "x": return x^e (mod n)
function RSADoPublic(x) {
	return x.modPowInt(this.e, this.n);
}

// Return the PKCS#1 RSA encryption of "text" as an even-length hex string
function RSAEncrypt(text) {
	var m = pkcs1pad2(text, (this.n.bitLength() + 7) >> 3);
	if (m == null) return null;
	var c = this.doPublic(m);
	if (c == null) return null;
	var h = c.toString(16);
	if ((h.length & 1) == 0) return h; else return "0" + h;
}

// Return the PKCS#1 OAEP RSA encryption of "text" as an even-length hex string
function RSAEncryptOAEP(text, hash, hashLen) {
	var m = oaep_pad(text, (this.n.bitLength() + 7) >> 3, hash, hashLen);
	if (m == null) return null;
	var c = this.doPublic(m);
	if (c == null) return null;
	var h = c.toString(16);
	if ((h.length & 1) == 0) return h; else return "0" + h;
}

// Return the PKCS#1 RSA encryption of "text" as a Base64-encoded string
//function RSAEncryptB64(text) {
//  var h = this.encrypt(text);
//  if(h) return hex2b64(h); else return null;
//}

// protected
RSAKey.prototype.doPublic = RSADoPublic;

// public
RSAKey.prototype.setPublic = RSASetPublic;
RSAKey.prototype.encrypt = RSAEncrypt;
RSAKey.prototype.encryptOAEP = RSAEncryptOAEP;
//RSAKey.prototype.encrypt_b64 = RSAEncryptB64;

RSAKey.prototype.type = "RSA";

; (function (root, factory) {
	if (typeof exports === "object") {
		// CommonJS
		module.exports = exports = factory();
	}
	else if (typeof define === "function" && define.amd) {
		// AMD
		define([], factory);
	}
	else {
		// Global (browser)
		root.CryptoJS = factory();
	}
}(this, function () {

	/*globals window, global, require*/

	/**
	 * CryptoJS core components.
	 */
	var CryptoJS = CryptoJS || (function (Math, undefined) {

		var crypto;

		// Native crypto from window (Browser)
		if (typeof window !== 'undefined' && window.crypto) {
			crypto = window.crypto;
		}

		// Native (experimental IE 11) crypto from window (Browser)
		if (!crypto && typeof window !== 'undefined' && window.msCrypto) {
			crypto = window.msCrypto;
		}

		// Native crypto from global (NodeJS)
		if (!crypto && typeof global !== 'undefined' && global.crypto) {
			crypto = global.crypto;
		}

		// Native crypto import via require (NodeJS)
		if (!crypto && typeof require === 'function') {
			try {
				crypto = require('crypto');
			} catch (err) { }
		}

		/*
		 * Cryptographically secure pseudorandom number generator
		 *
		 * As Math.random() is cryptographically not safe to use
		 */
		var cryptoSecureRandomInt = function () {
			if (crypto) {
				// Use getRandomValues method (Browser)
				if (typeof crypto.getRandomValues === 'function') {
					try {
						return crypto.getRandomValues(new Uint32Array(1))[0];
					} catch (err) { }
				}

				// Use randomBytes method (NodeJS)
				if (typeof crypto.randomBytes === 'function') {
					try {
						return crypto.randomBytes(4).readInt32LE();
					} catch (err) { }
				}
			}
			// 兼容低版本浏览器
			else {
				var rcache,
					r = (function (m_w) {
						var m_w = m_w;
						var m_z = 0x3ade68b1;
						var mask = 0xffffffff;

						return function () {
							m_z = (0x9069 * (m_z & 0xFFFF) + (m_z >> 0x10)) & mask;
							m_w = (0x4650 * (m_w & 0xFFFF) + (m_w >> 0x10)) & mask;
							var result = ((m_z << 0x10) + m_w) & mask;
							result /= 0x100000000;
							result += 0.5;
							return result * (Math.random() > .5 ? 1 : -1);
						}
					});
				var _r = r((rcache || Math.random()) * 0x100000000);
				rcache = _r() * 0x3ade67b7;
				return (_r() * 0x100000000) | 0;
			}

		};

		/*
		 * Local polyfill of Object.create

		 */
		var create = Object.create || (function () {
			function F() { }

			return function (obj) {
				var subtype;

				F.prototype = obj;

				subtype = new F();

				F.prototype = null;

				return subtype;
			};
		}())

		/**
		 * CryptoJS namespace.
		 */
		var C = {};

		/**
		 * Library namespace.
		 */
		var C_lib = C.lib = {};

		/**
		 * Base object for prototypal inheritance.
		 */
		var Base = C_lib.Base = (function () {


			return {
				/**
				 * Creates a new object that inherits from this object.
				 *
				 * @param {Object} overrides Properties to copy into the new object.
				 *
				 * @return {Object} The new object.
				 *
				 * @static
				 *
				 * @example
				 *
				 *     var MyType = CryptoJS.lib.Base.extend({
				 *         field: 'value',
				 *
				 *         method: function () {
				 *         }
				 *     });
				 */
				extend: function (overrides) {
					// Spawn
					var subtype = create(this);

					// Augment
					if (overrides) {
						subtype.mixIn(overrides);
					}

					// Create default initializer
					if (!subtype.hasOwnProperty('init') || this.init === subtype.init) {
						subtype.init = function () {
							subtype.$super.init.apply(this, arguments);
						};
					}

					// Initializer's prototype is the subtype object
					subtype.init.prototype = subtype;

					// Reference supertype
					subtype.$super = this;

					return subtype;
				},

				/**
				 * Extends this object and runs the init method.
				 * Arguments to create() will be passed to init().
				 *
				 * @return {Object} The new object.
				 *
				 * @static
				 *
				 * @example
				 *
				 *     var instance = MyType.create();
				 */
				create: function () {
					var instance = this.extend();
					instance.init.apply(instance, arguments);

					return instance;
				},

				/**
				 * Initializes a newly created object.
				 * Override this method to add some logic when your objects are created.
				 *
				 * @example
				 *
				 *     var MyType = CryptoJS.lib.Base.extend({
				 *         init: function () {
				 *             // ...
				 *         }
				 *     });
				 */
				init: function () {
				},

				/**
				 * Copies properties into this object.
				 *
				 * @param {Object} properties The properties to mix in.
				 *
				 * @example
				 *
				 *     MyType.mixIn({
				 *         field: 'value'
				 *     });
				 */
				mixIn: function (properties) {
					for (var propertyName in properties) {
						if (properties.hasOwnProperty(propertyName)) {
							this[propertyName] = properties[propertyName];
						}
					}

					// IE won't copy toString using the loop above
					if (properties.hasOwnProperty('toString')) {
						this.toString = properties.toString;
					}
				},

				/**
				 * Creates a copy of this object.
				 *
				 * @return {Object} The clone.
				 *
				 * @example
				 *
				 *     var clone = instance.clone();
				 */
				clone: function () {
					return this.init.prototype.extend(this);
				}
			};
		}());

		/**
		 * An array of 32-bit words.
		 *
		 * @property {Array} words The array of 32-bit words.
		 * @property {number} sigBytes The number of significant bytes in this word array.
		 */
		var WordArray = C_lib.WordArray = Base.extend({
			/**
			 * Initializes a newly created word array.
			 *
			 * @param {Array} words (Optional) An array of 32-bit words.
			 * @param {number} sigBytes (Optional) The number of significant bytes in the words.
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.lib.WordArray.create();
			 *     var wordArray = CryptoJS.lib.WordArray.create([0x00010203, 0x04050607]);
			 *     var wordArray = CryptoJS.lib.WordArray.create([0x00010203, 0x04050607], 6);
			 */
			init: function (words, sigBytes) {
				words = this.words = words || [];

				if (sigBytes != undefined) {
					this.sigBytes = sigBytes;
				} else {
					this.sigBytes = words.length * 4;
				}
			},

			/**
			 * Converts this word array to a string.
			 *
			 * @param {Encoder} encoder (Optional) The encoding strategy to use. Default: CryptoJS.enc.Hex
			 *
			 * @return {string} The stringified word array.
			 *
			 * @example
			 *
			 *     var string = wordArray + '';
			 *     var string = wordArray.toString();
			 *     var string = wordArray.toString(CryptoJS.enc.Utf8);
			 */
			toString: function (encoder) {
				return (encoder || Hex).stringify(this);
			},

			/**
			 * Concatenates a word array to this word array.
			 *
			 * @param {WordArray} wordArray The word array to append.
			 *
			 * @return {WordArray} This word array.
			 *
			 * @example
			 *
			 *     wordArray1.concat(wordArray2);
			 */
			concat: function (wordArray) {
				// Shortcuts
				var thisWords = this.words;
				var thatWords = wordArray.words;
				var thisSigBytes = this.sigBytes;
				var thatSigBytes = wordArray.sigBytes;

				// Clamp excess bits
				this.clamp();

				// Concat
				if (thisSigBytes % 4) {
					// Copy one byte at a time
					for (var i = 0; i < thatSigBytes; i++) {
						var thatByte = (thatWords[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff;
						thisWords[(thisSigBytes + i) >>> 2] |= thatByte << (24 - ((thisSigBytes + i) % 4) * 8);
					}
				} else {
					// Copy one word at a time
					for (var i = 0; i < thatSigBytes; i += 4) {
						thisWords[(thisSigBytes + i) >>> 2] = thatWords[i >>> 2];
					}
				}
				this.sigBytes += thatSigBytes;

				// Chainable
				return this;
			},

			/**
			 * Removes insignificant bits.
			 *
			 * @example
			 *
			 *     wordArray.clamp();
			 */
			clamp: function () {
				// Shortcuts
				var words = this.words;
				var sigBytes = this.sigBytes;

				// Clamp
				words[sigBytes >>> 2] &= 0xffffffff << (32 - (sigBytes % 4) * 8);
				words.length = Math.ceil(sigBytes / 4);
			},

			/**
			 * Creates a copy of this word array.
			 *
			 * @return {WordArray} The clone.
			 *
			 * @example
			 *
			 *     var clone = wordArray.clone();
			 */
			clone: function () {
				var clone = Base.clone.call(this);
				clone.words = this.words.slice(0);

				return clone;
			},

			/**
			 * Creates a word array filled with random bytes.
			 *
			 * @param {number} nBytes The number of random bytes to generate.
			 *
			 * @return {WordArray} The random word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.lib.WordArray.random(16);
			 */
			random: function (nBytes) {
				var words = [];

				for (var i = 0; i < nBytes; i += 4) {
					words.push(cryptoSecureRandomInt());
				}

				return new WordArray.init(words, nBytes);
			}
		});

		/**
		 * Encoder namespace.
		 */
		var C_enc = C.enc = {};

		/**
		 * Hex encoding strategy.
		 */
		var Hex = C_enc.Hex = {
			/**
			 * Converts a word array to a hex string.
			 *
			 * @param {WordArray} wordArray The word array.
			 *
			 * @return {string} The hex string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var hexString = CryptoJS.enc.Hex.stringify(wordArray);
			 */
			stringify: function (wordArray) {
				// Shortcuts
				var words = wordArray.words;
				var sigBytes = wordArray.sigBytes;

				// Convert
				var hexChars = [];
				for (var i = 0; i < sigBytes; i++) {
					var bite = (words[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff;
					hexChars.push((bite >>> 4).toString(16));
					hexChars.push((bite & 0x0f).toString(16));
				}

				return hexChars.join('');
			},

			/**
			 * Converts a hex string to a word array.
			 *
			 * @param {string} hexStr The hex string.
			 *
			 * @return {WordArray} The word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.enc.Hex.parse(hexString);
			 */
			parse: function (hexStr) {
				// Shortcut
				var hexStrLength = hexStr.length;

				// Convert
				var words = [];
				for (var i = 0; i < hexStrLength; i += 2) {
					words[i >>> 3] |= parseInt(hexStr.substr(i, 2), 16) << (24 - (i % 8) * 4);
				}

				return new WordArray.init(words, hexStrLength / 2);
			}
		};

		/**
		 * Latin1 encoding strategy.
		 */
		var Latin1 = C_enc.Latin1 = {
			/**
			 * Converts a word array to a Latin1 string.
			 *
			 * @param {WordArray} wordArray The word array.
			 *
			 * @return {string} The Latin1 string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var latin1String = CryptoJS.enc.Latin1.stringify(wordArray);
			 */
			stringify: function (wordArray) {
				// Shortcuts
				var words = wordArray.words;
				var sigBytes = wordArray.sigBytes;

				// Convert
				var latin1Chars = [];
				for (var i = 0; i < sigBytes; i++) {
					var bite = (words[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff;
					latin1Chars.push(String.fromCharCode(bite));
				}

				return latin1Chars.join('');
			},

			/**
			 * Converts a Latin1 string to a word array.
			 *
			 * @param {string} latin1Str The Latin1 string.
			 *
			 * @return {WordArray} The word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.enc.Latin1.parse(latin1String);
			 */
			parse: function (latin1Str) {
				// Shortcut
				var latin1StrLength = latin1Str.length;

				// Convert
				var words = [];
				for (var i = 0; i < latin1StrLength; i++) {
					words[i >>> 2] |= (latin1Str.charCodeAt(i) & 0xff) << (24 - (i % 4) * 8);
				}

				return new WordArray.init(words, latin1StrLength);
			}
		};

		/**
		 * UTF-8 encoding strategy.
		 */
		var Utf8 = C_enc.Utf8 = {
			/**
			 * Converts a word array to a UTF-8 string.
			 *
			 * @param {WordArray} wordArray The word array.
			 *
			 * @return {string} The UTF-8 string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var utf8String = CryptoJS.enc.Utf8.stringify(wordArray);
			 */
			stringify: function (wordArray) {
				try {
					return decodeURIComponent(escape(Latin1.stringify(wordArray)));
				} catch (e) {
					throw new Error('Malformed UTF-8 data');
				}
			},

			/**
			 * Converts a UTF-8 string to a word array.
			 *
			 * @param {string} utf8Str The UTF-8 string.
			 *
			 * @return {WordArray} The word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.enc.Utf8.parse(utf8String);
			 */
			parse: function (utf8Str) {
				return Latin1.parse(unescape(encodeURIComponent(utf8Str)));
			}
		};

		/**
		 * Abstract buffered block algorithm template.
		 *
		 * The property blockSize must be implemented in a concrete subtype.
		 *
		 * @property {number} _minBufferSize The number of blocks that should be kept unprocessed in the buffer. Default: 0
		 */
		var BufferedBlockAlgorithm = C_lib.BufferedBlockAlgorithm = Base.extend({
			/**
			 * Resets this block algorithm's data buffer to its initial state.
			 *
			 * @example
			 *
			 *     bufferedBlockAlgorithm.reset();
			 */
			reset: function () {
				// Initial values
				this._data = new WordArray.init();
				this._nDataBytes = 0;
			},

			/**
			 * Adds new data to this block algorithm's buffer.
			 *
			 * @param {WordArray|string} data The data to append. Strings are converted to a WordArray using UTF-8.
			 *
			 * @example
			 *
			 *     bufferedBlockAlgorithm._append('data');
			 *     bufferedBlockAlgorithm._append(wordArray);
			 */
			_append: function (data) {
				// Convert string to WordArray, else assume WordArray already
				if (typeof data == 'string') {
					data = Utf8.parse(data);
				}

				// Append
				this._data.concat(data);
				this._nDataBytes += data.sigBytes;
			},

			/**
			 * Processes available data blocks.
			 *
			 * This method invokes _doProcessBlock(offset), which must be implemented by a concrete subtype.
			 *
			 * @param {boolean} doFlush Whether all blocks and partial blocks should be processed.
			 *
			 * @return {WordArray} The processed data.
			 *
			 * @example
			 *
			 *     var processedData = bufferedBlockAlgorithm._process();
			 *     var processedData = bufferedBlockAlgorithm._process(!!'flush');
			 */
			_process: function (doFlush) {
				var processedWords;

				// Shortcuts
				var data = this._data;
				var dataWords = data.words;
				var dataSigBytes = data.sigBytes;
				var blockSize = this.blockSize;
				var blockSizeBytes = blockSize * 4;

				// Count blocks ready
				var nBlocksReady = dataSigBytes / blockSizeBytes;
				if (doFlush) {
					// Round up to include partial blocks
					nBlocksReady = Math.ceil(nBlocksReady);
				} else {
					// Round down to include only full blocks,
					// less the number of blocks that must remain in the buffer
					nBlocksReady = Math.max((nBlocksReady | 0) - this._minBufferSize, 0);
				}

				// Count words ready
				var nWordsReady = nBlocksReady * blockSize;

				// Count bytes ready
				var nBytesReady = Math.min(nWordsReady * 4, dataSigBytes);

				// Process blocks
				if (nWordsReady) {
					for (var offset = 0; offset < nWordsReady; offset += blockSize) {
						// Perform concrete-algorithm logic
						this._doProcessBlock(dataWords, offset);
					}

					// Remove processed words
					processedWords = dataWords.splice(0, nWordsReady);
					data.sigBytes -= nBytesReady;
				}

				// Return processed words
				return new WordArray.init(processedWords, nBytesReady);
			},

			/**
			 * Creates a copy of this object.
			 *
			 * @return {Object} The clone.
			 *
			 * @example
			 *
			 *     var clone = bufferedBlockAlgorithm.clone();
			 */
			clone: function () {
				var clone = Base.clone.call(this);
				clone._data = this._data.clone();

				return clone;
			},

			_minBufferSize: 0
		});

		/**
		 * Abstract hasher template.
		 *
		 * @property {number} blockSize The number of 32-bit words this hasher operates on. Default: 16 (512 bits)
		 */
		var Hasher = C_lib.Hasher = BufferedBlockAlgorithm.extend({
			/**
			 * Configuration options.
			 */
			cfg: Base.extend(),

			/**
			 * Initializes a newly created hasher.
			 *
			 * @param {Object} cfg (Optional) The configuration options to use for this hash computation.
			 *
			 * @example
			 *
			 *     var hasher = CryptoJS.algo.SHA256.create();
			 */
			init: function (cfg) {
				// Apply config defaults
				this.cfg = this.cfg.extend(cfg);

				// Set initial values
				this.reset();
			},

			/**
			 * Resets this hasher to its initial state.
			 *
			 * @example
			 *
			 *     hasher.reset();
			 */
			reset: function () {
				// Reset data buffer
				BufferedBlockAlgorithm.reset.call(this);

				// Perform concrete-hasher logic
				this._doReset();
			},

			/**
			 * Updates this hasher with a message.
			 *
			 * @param {WordArray|string} messageUpdate The message to append.
			 *
			 * @return {Hasher} This hasher.
			 *
			 * @example
			 *
			 *     hasher.update('message');
			 *     hasher.update(wordArray);
			 */
			update: function (messageUpdate) {
				// Append
				this._append(messageUpdate);

				// Update the hash
				this._process();

				// Chainable
				return this;
			},

			/**
			 * Finalizes the hash computation.
			 * Note that the finalize operation is effectively a destructive, read-once operation.
			 *
			 * @param {WordArray|string} messageUpdate (Optional) A final message update.
			 *
			 * @return {WordArray} The hash.
			 *
			 * @example
			 *
			 *     var hash = hasher.finalize();
			 *     var hash = hasher.finalize('message');
			 *     var hash = hasher.finalize(wordArray);
			 */
			finalize: function (messageUpdate) {
				// Final message update
				if (messageUpdate) {
					this._append(messageUpdate);
				}

				// Perform concrete-hasher logic
				var hash = this._doFinalize();

				return hash;
			},

			blockSize: 512 / 32,

			/**
			 * Creates a shortcut function to a hasher's object interface.
			 *
			 * @param {Hasher} hasher The hasher to create a helper for.
			 *
			 * @return {Function} The shortcut function.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var SHA256 = CryptoJS.lib.Hasher._createHelper(CryptoJS.algo.SHA256);
			 */
			_createHelper: function (hasher) {
				return function (message, cfg) {
					return new hasher.init(cfg).finalize(message);
				};
			},

			/**
			 * Creates a shortcut function to the HMAC's object interface.
			 *
			 * @param {Hasher} hasher The hasher to use in this HMAC helper.
			 *
			 * @return {Function} The shortcut function.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var HmacSHA256 = CryptoJS.lib.Hasher._createHmacHelper(CryptoJS.algo.SHA256);
			 */
			_createHmacHelper: function (hasher) {
				return function (message, key) {
					return new C_algo.HMAC.init(hasher, key).finalize(message);
				};
			}
		});

		/**
		 * Algorithm namespace.
		 */
		var C_algo = C.algo = {};

		return C;
	}(Math));


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var C_enc = C.enc;

		/**
		 * Base64 encoding strategy.
		 */
		var Base64 = C_enc.Base64 = {
			/**
			 * Converts a word array to a Base64 string.
			 *
			 * @param {WordArray} wordArray The word array.
			 *
			 * @return {string} The Base64 string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var base64String = CryptoJS.enc.Base64.stringify(wordArray);
			 */
			stringify: function (wordArray) {
				// Shortcuts
				var words = wordArray.words;
				var sigBytes = wordArray.sigBytes;
				var map = this._map;

				// Clamp excess bits
				wordArray.clamp();

				// Convert
				var base64Chars = [];
				for (var i = 0; i < sigBytes; i += 3) {
					var byte1 = (words[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff;
					var byte2 = (words[(i + 1) >>> 2] >>> (24 - ((i + 1) % 4) * 8)) & 0xff;
					var byte3 = (words[(i + 2) >>> 2] >>> (24 - ((i + 2) % 4) * 8)) & 0xff;

					var triplet = (byte1 << 16) | (byte2 << 8) | byte3;

					for (var j = 0; (j < 4) && (i + j * 0.75 < sigBytes); j++) {
						base64Chars.push(map.charAt((triplet >>> (6 * (3 - j))) & 0x3f));
					}
				}

				// Add padding
				var paddingChar = map.charAt(64);
				if (paddingChar) {
					while (base64Chars.length % 4) {
						base64Chars.push(paddingChar);
					}
				}

				return base64Chars.join('');
			},

			/**
			 * Converts a Base64 string to a word array.
			 *
			 * @param {string} base64Str The Base64 string.
			 *
			 * @return {WordArray} The word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.enc.Base64.parse(base64String);
			 */
			parse: function (base64Str) {
				// Shortcuts
				var base64StrLength = base64Str.length;
				var map = this._map;
				var reverseMap = this._reverseMap;

				if (!reverseMap) {
					reverseMap = this._reverseMap = [];
					for (var j = 0; j < map.length; j++) {
						reverseMap[map.charCodeAt(j)] = j;
					}
				}

				// Ignore padding
				var paddingChar = map.charAt(64);
				if (paddingChar) {
					var paddingIndex = base64Str.indexOf(paddingChar);
					if (paddingIndex !== -1) {
						base64StrLength = paddingIndex;
					}
				}

				// Convert
				return parseLoop(base64Str, base64StrLength, reverseMap);

			},

			_map: 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/='
		};

		function parseLoop(base64Str, base64StrLength, reverseMap) {
			var words = [];
			var nBytes = 0;
			for (var i = 0; i < base64StrLength; i++) {
				if (i % 4) {
					var bits1 = reverseMap[base64Str.charCodeAt(i - 1)] << ((i % 4) * 2);
					var bits2 = reverseMap[base64Str.charCodeAt(i)] >>> (6 - (i % 4) * 2);
					var bitsCombined = bits1 | bits2;
					words[nBytes >>> 2] |= bitsCombined << (24 - (nBytes % 4) * 8);
					nBytes++;
				}
			}
			return WordArray.create(words, nBytes);
		}
	}());


	(function (Math) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var Hasher = C_lib.Hasher;
		var C_algo = C.algo;

		// Constants table
		var T = [];

		// Compute constants
		(function () {
			for (var i = 0; i < 64; i++) {
				T[i] = (Math.abs(Math.sin(i + 1)) * 0x100000000) | 0;
			}
		}());

		/**
		 * MD5 hash algorithm.
		 */
		var MD5 = C_algo.MD5 = Hasher.extend({
			_doReset: function () {
				this._hash = new WordArray.init([
					0x67452301, 0xefcdab89,
					0x98badcfe, 0x10325476
				]);
			},

			_doProcessBlock: function (M, offset) {
				// Swap endian
				for (var i = 0; i < 16; i++) {
					// Shortcuts
					var offset_i = offset + i;
					var M_offset_i = M[offset_i];

					M[offset_i] = (
						(((M_offset_i << 8) | (M_offset_i >>> 24)) & 0x00ff00ff) |
						(((M_offset_i << 24) | (M_offset_i >>> 8)) & 0xff00ff00)
					);
				}

				// Shortcuts
				var H = this._hash.words;

				var M_offset_0 = M[offset + 0];
				var M_offset_1 = M[offset + 1];
				var M_offset_2 = M[offset + 2];
				var M_offset_3 = M[offset + 3];
				var M_offset_4 = M[offset + 4];
				var M_offset_5 = M[offset + 5];
				var M_offset_6 = M[offset + 6];
				var M_offset_7 = M[offset + 7];
				var M_offset_8 = M[offset + 8];
				var M_offset_9 = M[offset + 9];
				var M_offset_10 = M[offset + 10];
				var M_offset_11 = M[offset + 11];
				var M_offset_12 = M[offset + 12];
				var M_offset_13 = M[offset + 13];
				var M_offset_14 = M[offset + 14];
				var M_offset_15 = M[offset + 15];

				// Working varialbes
				var a = H[0];
				var b = H[1];
				var c = H[2];
				var d = H[3];

				// Computation
				a = FF(a, b, c, d, M_offset_0, 7, T[0]);
				d = FF(d, a, b, c, M_offset_1, 12, T[1]);
				c = FF(c, d, a, b, M_offset_2, 17, T[2]);
				b = FF(b, c, d, a, M_offset_3, 22, T[3]);
				a = FF(a, b, c, d, M_offset_4, 7, T[4]);
				d = FF(d, a, b, c, M_offset_5, 12, T[5]);
				c = FF(c, d, a, b, M_offset_6, 17, T[6]);
				b = FF(b, c, d, a, M_offset_7, 22, T[7]);
				a = FF(a, b, c, d, M_offset_8, 7, T[8]);
				d = FF(d, a, b, c, M_offset_9, 12, T[9]);
				c = FF(c, d, a, b, M_offset_10, 17, T[10]);
				b = FF(b, c, d, a, M_offset_11, 22, T[11]);
				a = FF(a, b, c, d, M_offset_12, 7, T[12]);
				d = FF(d, a, b, c, M_offset_13, 12, T[13]);
				c = FF(c, d, a, b, M_offset_14, 17, T[14]);
				b = FF(b, c, d, a, M_offset_15, 22, T[15]);

				a = GG(a, b, c, d, M_offset_1, 5, T[16]);
				d = GG(d, a, b, c, M_offset_6, 9, T[17]);
				c = GG(c, d, a, b, M_offset_11, 14, T[18]);
				b = GG(b, c, d, a, M_offset_0, 20, T[19]);
				a = GG(a, b, c, d, M_offset_5, 5, T[20]);
				d = GG(d, a, b, c, M_offset_10, 9, T[21]);
				c = GG(c, d, a, b, M_offset_15, 14, T[22]);
				b = GG(b, c, d, a, M_offset_4, 20, T[23]);
				a = GG(a, b, c, d, M_offset_9, 5, T[24]);
				d = GG(d, a, b, c, M_offset_14, 9, T[25]);
				c = GG(c, d, a, b, M_offset_3, 14, T[26]);
				b = GG(b, c, d, a, M_offset_8, 20, T[27]);
				a = GG(a, b, c, d, M_offset_13, 5, T[28]);
				d = GG(d, a, b, c, M_offset_2, 9, T[29]);
				c = GG(c, d, a, b, M_offset_7, 14, T[30]);
				b = GG(b, c, d, a, M_offset_12, 20, T[31]);

				a = HH(a, b, c, d, M_offset_5, 4, T[32]);
				d = HH(d, a, b, c, M_offset_8, 11, T[33]);
				c = HH(c, d, a, b, M_offset_11, 16, T[34]);
				b = HH(b, c, d, a, M_offset_14, 23, T[35]);
				a = HH(a, b, c, d, M_offset_1, 4, T[36]);
				d = HH(d, a, b, c, M_offset_4, 11, T[37]);
				c = HH(c, d, a, b, M_offset_7, 16, T[38]);
				b = HH(b, c, d, a, M_offset_10, 23, T[39]);
				a = HH(a, b, c, d, M_offset_13, 4, T[40]);
				d = HH(d, a, b, c, M_offset_0, 11, T[41]);
				c = HH(c, d, a, b, M_offset_3, 16, T[42]);
				b = HH(b, c, d, a, M_offset_6, 23, T[43]);
				a = HH(a, b, c, d, M_offset_9, 4, T[44]);
				d = HH(d, a, b, c, M_offset_12, 11, T[45]);
				c = HH(c, d, a, b, M_offset_15, 16, T[46]);
				b = HH(b, c, d, a, M_offset_2, 23, T[47]);

				a = II(a, b, c, d, M_offset_0, 6, T[48]);
				d = II(d, a, b, c, M_offset_7, 10, T[49]);
				c = II(c, d, a, b, M_offset_14, 15, T[50]);
				b = II(b, c, d, a, M_offset_5, 21, T[51]);
				a = II(a, b, c, d, M_offset_12, 6, T[52]);
				d = II(d, a, b, c, M_offset_3, 10, T[53]);
				c = II(c, d, a, b, M_offset_10, 15, T[54]);
				b = II(b, c, d, a, M_offset_1, 21, T[55]);
				a = II(a, b, c, d, M_offset_8, 6, T[56]);
				d = II(d, a, b, c, M_offset_15, 10, T[57]);
				c = II(c, d, a, b, M_offset_6, 15, T[58]);
				b = II(b, c, d, a, M_offset_13, 21, T[59]);
				a = II(a, b, c, d, M_offset_4, 6, T[60]);
				d = II(d, a, b, c, M_offset_11, 10, T[61]);
				c = II(c, d, a, b, M_offset_2, 15, T[62]);
				b = II(b, c, d, a, M_offset_9, 21, T[63]);

				// Intermediate hash value
				H[0] = (H[0] + a) | 0;
				H[1] = (H[1] + b) | 0;
				H[2] = (H[2] + c) | 0;
				H[3] = (H[3] + d) | 0;
			},

			_doFinalize: function () {
				// Shortcuts
				var data = this._data;
				var dataWords = data.words;

				var nBitsTotal = this._nDataBytes * 8;
				var nBitsLeft = data.sigBytes * 8;

				// Add padding
				dataWords[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);

				var nBitsTotalH = Math.floor(nBitsTotal / 0x100000000);
				var nBitsTotalL = nBitsTotal;
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 15] = (
					(((nBitsTotalH << 8) | (nBitsTotalH >>> 24)) & 0x00ff00ff) |
					(((nBitsTotalH << 24) | (nBitsTotalH >>> 8)) & 0xff00ff00)
				);
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 14] = (
					(((nBitsTotalL << 8) | (nBitsTotalL >>> 24)) & 0x00ff00ff) |
					(((nBitsTotalL << 24) | (nBitsTotalL >>> 8)) & 0xff00ff00)
				);

				data.sigBytes = (dataWords.length + 1) * 4;

				// Hash final blocks
				this._process();

				// Shortcuts
				var hash = this._hash;
				var H = hash.words;

				// Swap endian
				for (var i = 0; i < 4; i++) {
					// Shortcut
					var H_i = H[i];

					H[i] = (((H_i << 8) | (H_i >>> 24)) & 0x00ff00ff) |
						(((H_i << 24) | (H_i >>> 8)) & 0xff00ff00);
				}

				// Return final computed hash
				return hash;
			},

			clone: function () {
				var clone = Hasher.clone.call(this);
				clone._hash = this._hash.clone();

				return clone;
			}
		});

		function FF(a, b, c, d, x, s, t) {
			var n = a + ((b & c) | (~b & d)) + x + t;
			return ((n << s) | (n >>> (32 - s))) + b;
		}

		function GG(a, b, c, d, x, s, t) {
			var n = a + ((b & d) | (c & ~d)) + x + t;
			return ((n << s) | (n >>> (32 - s))) + b;
		}

		function HH(a, b, c, d, x, s, t) {
			var n = a + (b ^ c ^ d) + x + t;
			return ((n << s) | (n >>> (32 - s))) + b;
		}

		function II(a, b, c, d, x, s, t) {
			var n = a + (c ^ (b | ~d)) + x + t;
			return ((n << s) | (n >>> (32 - s))) + b;
		}

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.MD5('message');
		 *     var hash = CryptoJS.MD5(wordArray);
		 */
		C.MD5 = Hasher._createHelper(MD5);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacMD5(message, key);
		 */
		C.HmacMD5 = Hasher._createHmacHelper(MD5);
	}(Math));


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var Hasher = C_lib.Hasher;
		var C_algo = C.algo;

		// Reusable object
		var W = [];

		/**
		 * SHA-1 hash algorithm.
		 */
		var SHA1 = C_algo.SHA1 = Hasher.extend({
			_doReset: function () {
				this._hash = new WordArray.init([
					0x67452301, 0xefcdab89,
					0x98badcfe, 0x10325476,
					0xc3d2e1f0
				]);
			},

			_doProcessBlock: function (M, offset) {
				// Shortcut
				var H = this._hash.words;

				// Working variables
				var a = H[0];
				var b = H[1];
				var c = H[2];
				var d = H[3];
				var e = H[4];

				// Computation
				for (var i = 0; i < 80; i++) {
					if (i < 16) {
						W[i] = M[offset + i] | 0;
					} else {
						var n = W[i - 3] ^ W[i - 8] ^ W[i - 14] ^ W[i - 16];
						W[i] = (n << 1) | (n >>> 31);
					}

					var t = ((a << 5) | (a >>> 27)) + e + W[i];
					if (i < 20) {
						t += ((b & c) | (~b & d)) + 0x5a827999;
					} else if (i < 40) {
						t += (b ^ c ^ d) + 0x6ed9eba1;
					} else if (i < 60) {
						t += ((b & c) | (b & d) | (c & d)) - 0x70e44324;
					} else /* if (i < 80) */ {
						t += (b ^ c ^ d) - 0x359d3e2a;
					}

					e = d;
					d = c;
					c = (b << 30) | (b >>> 2);
					b = a;
					a = t;
				}

				// Intermediate hash value
				H[0] = (H[0] + a) | 0;
				H[1] = (H[1] + b) | 0;
				H[2] = (H[2] + c) | 0;
				H[3] = (H[3] + d) | 0;
				H[4] = (H[4] + e) | 0;
			},

			_doFinalize: function () {
				// Shortcuts
				var data = this._data;
				var dataWords = data.words;

				var nBitsTotal = this._nDataBytes * 8;
				var nBitsLeft = data.sigBytes * 8;

				// Add padding
				dataWords[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 14] = Math.floor(nBitsTotal / 0x100000000);
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 15] = nBitsTotal;
				data.sigBytes = dataWords.length * 4;

				// Hash final blocks
				this._process();

				// Return final computed hash
				return this._hash;
			},

			clone: function () {
				var clone = Hasher.clone.call(this);
				clone._hash = this._hash.clone();

				return clone;
			}
		});

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.SHA1('message');
		 *     var hash = CryptoJS.SHA1(wordArray);
		 */
		C.SHA1 = Hasher._createHelper(SHA1);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacSHA1(message, key);
		 */
		C.HmacSHA1 = Hasher._createHmacHelper(SHA1);
	}());


	(function (Math) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var Hasher = C_lib.Hasher;
		var C_algo = C.algo;

		// Initialization and round constants tables
		var H = [];
		var K = [];

		// Compute constants
		(function () {
			function isPrime(n) {
				var sqrtN = Math.sqrt(n);
				for (var factor = 2; factor <= sqrtN; factor++) {
					if (!(n % factor)) {
						return false;
					}
				}

				return true;
			}

			function getFractionalBits(n) {
				return ((n - (n | 0)) * 0x100000000) | 0;
			}

			var n = 2;
			var nPrime = 0;
			while (nPrime < 64) {
				if (isPrime(n)) {
					if (nPrime < 8) {
						H[nPrime] = getFractionalBits(Math.pow(n, 1 / 2));
					}
					K[nPrime] = getFractionalBits(Math.pow(n, 1 / 3));

					nPrime++;
				}

				n++;
			}
		}());

		// Reusable object
		var W = [];

		/**
		 * SHA-256 hash algorithm.
		 */
		var SHA256 = C_algo.SHA256 = Hasher.extend({
			_doReset: function () {
				this._hash = new WordArray.init(H.slice(0));
			},

			_doProcessBlock: function (M, offset) {
				// Shortcut
				var H = this._hash.words;

				// Working variables
				var a = H[0];
				var b = H[1];
				var c = H[2];
				var d = H[3];
				var e = H[4];
				var f = H[5];
				var g = H[6];
				var h = H[7];

				// Computation
				for (var i = 0; i < 64; i++) {
					if (i < 16) {
						W[i] = M[offset + i] | 0;
					} else {
						var gamma0x = W[i - 15];
						var gamma0 = ((gamma0x << 25) | (gamma0x >>> 7)) ^
							((gamma0x << 14) | (gamma0x >>> 18)) ^
							(gamma0x >>> 3);

						var gamma1x = W[i - 2];
						var gamma1 = ((gamma1x << 15) | (gamma1x >>> 17)) ^
							((gamma1x << 13) | (gamma1x >>> 19)) ^
							(gamma1x >>> 10);

						W[i] = gamma0 + W[i - 7] + gamma1 + W[i - 16];
					}

					var ch = (e & f) ^ (~e & g);
					var maj = (a & b) ^ (a & c) ^ (b & c);

					var sigma0 = ((a << 30) | (a >>> 2)) ^ ((a << 19) | (a >>> 13)) ^ ((a << 10) | (a >>> 22));
					var sigma1 = ((e << 26) | (e >>> 6)) ^ ((e << 21) | (e >>> 11)) ^ ((e << 7) | (e >>> 25));

					var t1 = h + sigma1 + ch + K[i] + W[i];
					var t2 = sigma0 + maj;

					h = g;
					g = f;
					f = e;
					e = (d + t1) | 0;
					d = c;
					c = b;
					b = a;
					a = (t1 + t2) | 0;
				}

				// Intermediate hash value
				H[0] = (H[0] + a) | 0;
				H[1] = (H[1] + b) | 0;
				H[2] = (H[2] + c) | 0;
				H[3] = (H[3] + d) | 0;
				H[4] = (H[4] + e) | 0;
				H[5] = (H[5] + f) | 0;
				H[6] = (H[6] + g) | 0;
				H[7] = (H[7] + h) | 0;
			},

			_doFinalize: function () {
				// Shortcuts
				var data = this._data;
				var dataWords = data.words;

				var nBitsTotal = this._nDataBytes * 8;
				var nBitsLeft = data.sigBytes * 8;

				// Add padding
				dataWords[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 14] = Math.floor(nBitsTotal / 0x100000000);
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 15] = nBitsTotal;
				data.sigBytes = dataWords.length * 4;

				// Hash final blocks
				this._process();

				// Return final computed hash
				return this._hash;
			},

			clone: function () {
				var clone = Hasher.clone.call(this);
				clone._hash = this._hash.clone();

				return clone;
			}
		});

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.SHA256('message');
		 *     var hash = CryptoJS.SHA256(wordArray);
		 */
		C.SHA256 = Hasher._createHelper(SHA256);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacSHA256(message, key);
		 */
		C.HmacSHA256 = Hasher._createHmacHelper(SHA256);
	}(Math));


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var C_enc = C.enc;

		/**
		 * UTF-16 BE encoding strategy.
		 */
		var Utf16BE = C_enc.Utf16 = C_enc.Utf16BE = {
			/**
			 * Converts a word array to a UTF-16 BE string.
			 *
			 * @param {WordArray} wordArray The word array.
			 *
			 * @return {string} The UTF-16 BE string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var utf16String = CryptoJS.enc.Utf16.stringify(wordArray);
			 */
			stringify: function (wordArray) {
				// Shortcuts
				var words = wordArray.words;
				var sigBytes = wordArray.sigBytes;

				// Convert
				var utf16Chars = [];
				for (var i = 0; i < sigBytes; i += 2) {
					var codePoint = (words[i >>> 2] >>> (16 - (i % 4) * 8)) & 0xffff;
					utf16Chars.push(String.fromCharCode(codePoint));
				}

				return utf16Chars.join('');
			},

			/**
			 * Converts a UTF-16 BE string to a word array.
			 *
			 * @param {string} utf16Str The UTF-16 BE string.
			 *
			 * @return {WordArray} The word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.enc.Utf16.parse(utf16String);
			 */
			parse: function (utf16Str) {
				// Shortcut
				var utf16StrLength = utf16Str.length;

				// Convert
				var words = [];
				for (var i = 0; i < utf16StrLength; i++) {
					words[i >>> 1] |= utf16Str.charCodeAt(i) << (16 - (i % 2) * 16);
				}

				return WordArray.create(words, utf16StrLength * 2);
			}
		};

		/**
		 * UTF-16 LE encoding strategy.
		 */
		C_enc.Utf16LE = {
			/**
			 * Converts a word array to a UTF-16 LE string.
			 *
			 * @param {WordArray} wordArray The word array.
			 *
			 * @return {string} The UTF-16 LE string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var utf16Str = CryptoJS.enc.Utf16LE.stringify(wordArray);
			 */
			stringify: function (wordArray) {
				// Shortcuts
				var words = wordArray.words;
				var sigBytes = wordArray.sigBytes;

				// Convert
				var utf16Chars = [];
				for (var i = 0; i < sigBytes; i += 2) {
					var codePoint = swapEndian((words[i >>> 2] >>> (16 - (i % 4) * 8)) & 0xffff);
					utf16Chars.push(String.fromCharCode(codePoint));
				}

				return utf16Chars.join('');
			},

			/**
			 * Converts a UTF-16 LE string to a word array.
			 *
			 * @param {string} utf16Str The UTF-16 LE string.
			 *
			 * @return {WordArray} The word array.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.enc.Utf16LE.parse(utf16Str);
			 */
			parse: function (utf16Str) {
				// Shortcut
				var utf16StrLength = utf16Str.length;

				// Convert
				var words = [];
				for (var i = 0; i < utf16StrLength; i++) {
					words[i >>> 1] |= swapEndian(utf16Str.charCodeAt(i) << (16 - (i % 2) * 16));
				}

				return WordArray.create(words, utf16StrLength * 2);
			}
		};

		function swapEndian(word) {
			return ((word << 8) & 0xff00ff00) | ((word >>> 8) & 0x00ff00ff);
		}
	}());


	(function () {
		// Check if typed arrays are supported
		if (typeof ArrayBuffer != 'function') {
			return;
		}

		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;

		// Reference original init
		var superInit = WordArray.init;

		// Augment WordArray.init to handle typed arrays
		var subInit = WordArray.init = function (typedArray) {
			// Convert buffers to uint8
			if (typedArray instanceof ArrayBuffer) {
				typedArray = new Uint8Array(typedArray);
			}

			// Convert other array views to uint8
			if (
				typedArray instanceof Int8Array ||
				(typeof Uint8ClampedArray !== "undefined" && typedArray instanceof Uint8ClampedArray) ||
				typedArray instanceof Int16Array ||
				typedArray instanceof Uint16Array ||
				typedArray instanceof Int32Array ||
				typedArray instanceof Uint32Array ||
				typedArray instanceof Float32Array ||
				typedArray instanceof Float64Array
			) {
				typedArray = new Uint8Array(typedArray.buffer, typedArray.byteOffset, typedArray.byteLength);
			}

			// Handle Uint8Array
			if (typedArray instanceof Uint8Array) {
				// Shortcut
				var typedArrayByteLength = typedArray.byteLength;

				// Extract bytes
				var words = [];
				for (var i = 0; i < typedArrayByteLength; i++) {
					words[i >>> 2] |= typedArray[i] << (24 - (i % 4) * 8);
				}

				// Initialize this word array
				superInit.call(this, words, typedArrayByteLength);
			} else {
				// Else call normal init
				superInit.apply(this, arguments);
			}
		};

		subInit.prototype = WordArray;
	}());


	/** @preserve
	(c) 2012 by Cédric Mesnil. All rights reserved.

	Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

		- Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
		- Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

	THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
	*/

	(function (Math) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var Hasher = C_lib.Hasher;
		var C_algo = C.algo;

		// Constants table
		var _zl = WordArray.create([
			0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
			7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
			3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
			1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
			4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]);
		var _zr = WordArray.create([
			5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
			6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
			15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
			8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
			12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]);
		var _sl = WordArray.create([
			11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
			7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
			11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
			11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
			9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]);
		var _sr = WordArray.create([
			8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
			9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
			9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
			15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
			8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]);

		var _hl = WordArray.create([0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]);
		var _hr = WordArray.create([0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]);

		/**
		 * RIPEMD160 hash algorithm.
		 */
		var RIPEMD160 = C_algo.RIPEMD160 = Hasher.extend({
			_doReset: function () {
				this._hash = WordArray.create([0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]);
			},

			_doProcessBlock: function (M, offset) {

				// Swap endian
				for (var i = 0; i < 16; i++) {
					// Shortcuts
					var offset_i = offset + i;
					var M_offset_i = M[offset_i];

					// Swap
					M[offset_i] = (
						(((M_offset_i << 8) | (M_offset_i >>> 24)) & 0x00ff00ff) |
						(((M_offset_i << 24) | (M_offset_i >>> 8)) & 0xff00ff00)
					);
				}
				// Shortcut
				var H = this._hash.words;
				var hl = _hl.words;
				var hr = _hr.words;
				var zl = _zl.words;
				var zr = _zr.words;
				var sl = _sl.words;
				var sr = _sr.words;

				// Working variables
				var al, bl, cl, dl, el;
				var ar, br, cr, dr, er;

				ar = al = H[0];
				br = bl = H[1];
				cr = cl = H[2];
				dr = dl = H[3];
				er = el = H[4];
				// Computation
				var t;
				for (var i = 0; i < 80; i += 1) {
					t = (al + M[offset + zl[i]]) | 0;
					if (i < 16) {
						t += f1(bl, cl, dl) + hl[0];
					} else if (i < 32) {
						t += f2(bl, cl, dl) + hl[1];
					} else if (i < 48) {
						t += f3(bl, cl, dl) + hl[2];
					} else if (i < 64) {
						t += f4(bl, cl, dl) + hl[3];
					} else {// if (i<80) {
						t += f5(bl, cl, dl) + hl[4];
					}
					t = t | 0;
					t = rotl(t, sl[i]);
					t = (t + el) | 0;
					al = el;
					el = dl;
					dl = rotl(cl, 10);
					cl = bl;
					bl = t;

					t = (ar + M[offset + zr[i]]) | 0;
					if (i < 16) {
						t += f5(br, cr, dr) + hr[0];
					} else if (i < 32) {
						t += f4(br, cr, dr) + hr[1];
					} else if (i < 48) {
						t += f3(br, cr, dr) + hr[2];
					} else if (i < 64) {
						t += f2(br, cr, dr) + hr[3];
					} else {// if (i<80) {
						t += f1(br, cr, dr) + hr[4];
					}
					t = t | 0;
					t = rotl(t, sr[i]);
					t = (t + er) | 0;
					ar = er;
					er = dr;
					dr = rotl(cr, 10);
					cr = br;
					br = t;
				}
				// Intermediate hash value
				t = (H[1] + cl + dr) | 0;
				H[1] = (H[2] + dl + er) | 0;
				H[2] = (H[3] + el + ar) | 0;
				H[3] = (H[4] + al + br) | 0;
				H[4] = (H[0] + bl + cr) | 0;
				H[0] = t;
			},

			_doFinalize: function () {
				// Shortcuts
				var data = this._data;
				var dataWords = data.words;

				var nBitsTotal = this._nDataBytes * 8;
				var nBitsLeft = data.sigBytes * 8;

				// Add padding
				dataWords[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);
				dataWords[(((nBitsLeft + 64) >>> 9) << 4) + 14] = (
					(((nBitsTotal << 8) | (nBitsTotal >>> 24)) & 0x00ff00ff) |
					(((nBitsTotal << 24) | (nBitsTotal >>> 8)) & 0xff00ff00)
				);
				data.sigBytes = (dataWords.length + 1) * 4;

				// Hash final blocks
				this._process();

				// Shortcuts
				var hash = this._hash;
				var H = hash.words;

				// Swap endian
				for (var i = 0; i < 5; i++) {
					// Shortcut
					var H_i = H[i];

					// Swap
					H[i] = (((H_i << 8) | (H_i >>> 24)) & 0x00ff00ff) |
						(((H_i << 24) | (H_i >>> 8)) & 0xff00ff00);
				}

				// Return final computed hash
				return hash;
			},

			clone: function () {
				var clone = Hasher.clone.call(this);
				clone._hash = this._hash.clone();

				return clone;
			}
		});


		function f1(x, y, z) {
			return ((x) ^ (y) ^ (z));

		}

		function f2(x, y, z) {
			return (((x) & (y)) | ((~x) & (z)));
		}

		function f3(x, y, z) {
			return (((x) | (~(y))) ^ (z));
		}

		function f4(x, y, z) {
			return (((x) & (z)) | ((y) & (~(z))));
		}

		function f5(x, y, z) {
			return ((x) ^ ((y) | (~(z))));

		}

		function rotl(x, n) {
			return (x << n) | (x >>> (32 - n));
		}


		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.RIPEMD160('message');
		 *     var hash = CryptoJS.RIPEMD160(wordArray);
		 */
		C.RIPEMD160 = Hasher._createHelper(RIPEMD160);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacRIPEMD160(message, key);
		 */
		C.HmacRIPEMD160 = Hasher._createHmacHelper(RIPEMD160);
	}(Math));


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var Base = C_lib.Base;
		var C_enc = C.enc;
		var Utf8 = C_enc.Utf8;
		var C_algo = C.algo;

		/**
		 * HMAC algorithm.
		 */
		var HMAC = C_algo.HMAC = Base.extend({
			/**
			 * Initializes a newly created HMAC.
			 *
			 * @param {Hasher} hasher The hash algorithm to use.
			 * @param {WordArray|string} key The secret key.
			 *
			 * @example
			 *
			 *     var hmacHasher = CryptoJS.algo.HMAC.create(CryptoJS.algo.SHA256, key);
			 */
			init: function (hasher, key) {
				// Init hasher
				hasher = this._hasher = new hasher.init();

				// Convert string to WordArray, else assume WordArray already
				if (typeof key == 'string') {
					key = Utf8.parse(key);
				}

				// Shortcuts
				var hasherBlockSize = hasher.blockSize;
				var hasherBlockSizeBytes = hasherBlockSize * 4;

				// Allow arbitrary length keys
				if (key.sigBytes > hasherBlockSizeBytes) {
					key = hasher.finalize(key);
				}

				// Clamp excess bits
				key.clamp();

				// Clone key for inner and outer pads
				var oKey = this._oKey = key.clone();
				var iKey = this._iKey = key.clone();

				// Shortcuts
				var oKeyWords = oKey.words;
				var iKeyWords = iKey.words;

				// XOR keys with pad constants
				for (var i = 0; i < hasherBlockSize; i++) {
					oKeyWords[i] ^= 0x5c5c5c5c;
					iKeyWords[i] ^= 0x36363636;
				}
				oKey.sigBytes = iKey.sigBytes = hasherBlockSizeBytes;

				// Set initial values
				this.reset();
			},

			/**
			 * Resets this HMAC to its initial state.
			 *
			 * @example
			 *
			 *     hmacHasher.reset();
			 */
			reset: function () {
				// Shortcut
				var hasher = this._hasher;

				// Reset
				hasher.reset();
				hasher.update(this._iKey);
			},

			/**
			 * Updates this HMAC with a message.
			 *
			 * @param {WordArray|string} messageUpdate The message to append.
			 *
			 * @return {HMAC} This HMAC instance.
			 *
			 * @example
			 *
			 *     hmacHasher.update('message');
			 *     hmacHasher.update(wordArray);
			 */
			update: function (messageUpdate) {
				this._hasher.update(messageUpdate);

				// Chainable
				return this;
			},

			/**
			 * Finalizes the HMAC computation.
			 * Note that the finalize operation is effectively a destructive, read-once operation.
			 *
			 * @param {WordArray|string} messageUpdate (Optional) A final message update.
			 *
			 * @return {WordArray} The HMAC.
			 *
			 * @example
			 *
			 *     var hmac = hmacHasher.finalize();
			 *     var hmac = hmacHasher.finalize('message');
			 *     var hmac = hmacHasher.finalize(wordArray);
			 */
			finalize: function (messageUpdate) {
				// Shortcut
				var hasher = this._hasher;

				// Compute HMAC
				var innerHash = hasher.finalize(messageUpdate);
				hasher.reset();
				var hmac = hasher.finalize(this._oKey.clone().concat(innerHash));

				return hmac;
			}
		});
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var Base = C_lib.Base;
		var WordArray = C_lib.WordArray;
		var C_algo = C.algo;
		var SHA1 = C_algo.SHA1;
		var HMAC = C_algo.HMAC;

		/**
		 * Password-Based Key Derivation Function 2 algorithm.
		 */
		var PBKDF2 = C_algo.PBKDF2 = Base.extend({
			/**
			 * Configuration options.
			 *
			 * @property {number} keySize The key size in words to generate. Default: 4 (128 bits)
			 * @property {Hasher} hasher The hasher to use. Default: SHA1
			 * @property {number} iterations The number of iterations to perform. Default: 1
			 */
			cfg: Base.extend({
				keySize: 128 / 32,
				hasher: SHA1,
				iterations: 1
			}),

			/**
			 * Initializes a newly created key derivation function.
			 *
			 * @param {Object} cfg (Optional) The configuration options to use for the derivation.
			 *
			 * @example
			 *
			 *     var kdf = CryptoJS.algo.PBKDF2.create();
			 *     var kdf = CryptoJS.algo.PBKDF2.create({ keySize: 8 });
			 *     var kdf = CryptoJS.algo.PBKDF2.create({ keySize: 8, iterations: 1000 });
			 */
			init: function (cfg) {
				this.cfg = this.cfg.extend(cfg);
			},

			/**
			 * Computes the Password-Based Key Derivation Function 2.
			 *
			 * @param {WordArray|string} password The password.
			 * @param {WordArray|string} salt A salt.
			 *
			 * @return {WordArray} The derived key.
			 *
			 * @example
			 *
			 *     var key = kdf.compute(password, salt);
			 */
			compute: function (password, salt) {
				// Shortcut
				var cfg = this.cfg;

				// Init HMAC
				var hmac = HMAC.create(cfg.hasher, password);

				// Initial values
				var derivedKey = WordArray.create();
				var blockIndex = WordArray.create([0x00000001]);

				// Shortcuts
				var derivedKeyWords = derivedKey.words;
				var blockIndexWords = blockIndex.words;
				var keySize = cfg.keySize;
				var iterations = cfg.iterations;

				// Generate key
				while (derivedKeyWords.length < keySize) {
					var block = hmac.update(salt).finalize(blockIndex);
					hmac.reset();

					// Shortcuts
					var blockWords = block.words;
					var blockWordsLength = blockWords.length;

					// Iterations
					var intermediate = block;
					for (var i = 1; i < iterations; i++) {
						intermediate = hmac.finalize(intermediate);
						hmac.reset();

						// Shortcut
						var intermediateWords = intermediate.words;

						// XOR intermediate with block
						for (var j = 0; j < blockWordsLength; j++) {
							blockWords[j] ^= intermediateWords[j];
						}
					}

					derivedKey.concat(block);
					blockIndexWords[0]++;
				}
				derivedKey.sigBytes = keySize * 4;

				return derivedKey;
			}
		});

		/**
		 * Computes the Password-Based Key Derivation Function 2.
		 *
		 * @param {WordArray|string} password The password.
		 * @param {WordArray|string} salt A salt.
		 * @param {Object} cfg (Optional) The configuration options to use for this computation.
		 *
		 * @return {WordArray} The derived key.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var key = CryptoJS.PBKDF2(password, salt);
		 *     var key = CryptoJS.PBKDF2(password, salt, { keySize: 8 });
		 *     var key = CryptoJS.PBKDF2(password, salt, { keySize: 8, iterations: 1000 });
		 */
		C.PBKDF2 = function (password, salt, cfg) {
			return PBKDF2.create(cfg).compute(password, salt);
		};
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var Base = C_lib.Base;
		var WordArray = C_lib.WordArray;
		var C_algo = C.algo;
		var MD5 = C_algo.MD5;

		/**
		 * This key derivation function is meant to conform with EVP_BytesToKey.
		 * www.openssl.org/docs/crypto/EVP_BytesToKey.html
		 */
		var EvpKDF = C_algo.EvpKDF = Base.extend({
			/**
			 * Configuration options.
			 *
			 * @property {number} keySize The key size in words to generate. Default: 4 (128 bits)
			 * @property {Hasher} hasher The hash algorithm to use. Default: MD5
			 * @property {number} iterations The number of iterations to perform. Default: 1
			 */
			cfg: Base.extend({
				keySize: 128 / 32,
				hasher: MD5,
				iterations: 1
			}),

			/**
			 * Initializes a newly created key derivation function.
			 *
			 * @param {Object} cfg (Optional) The configuration options to use for the derivation.
			 *
			 * @example
			 *
			 *     var kdf = CryptoJS.algo.EvpKDF.create();
			 *     var kdf = CryptoJS.algo.EvpKDF.create({ keySize: 8 });
			 *     var kdf = CryptoJS.algo.EvpKDF.create({ keySize: 8, iterations: 1000 });
			 */
			init: function (cfg) {
				this.cfg = this.cfg.extend(cfg);
			},

			/**
			 * Derives a key from a password.
			 *
			 * @param {WordArray|string} password The password.
			 * @param {WordArray|string} salt A salt.
			 *
			 * @return {WordArray} The derived key.
			 *
			 * @example
			 *
			 *     var key = kdf.compute(password, salt);
			 */
			compute: function (password, salt) {
				var block;

				// Shortcut
				var cfg = this.cfg;

				// Init hasher
				var hasher = cfg.hasher.create();

				// Initial values
				var derivedKey = WordArray.create();

				// Shortcuts
				var derivedKeyWords = derivedKey.words;
				var keySize = cfg.keySize;
				var iterations = cfg.iterations;

				// Generate key
				while (derivedKeyWords.length < keySize) {
					if (block) {
						hasher.update(block);
					}
					block = hasher.update(password).finalize(salt);
					hasher.reset();

					// Iterations
					for (var i = 1; i < iterations; i++) {
						block = hasher.finalize(block);
						hasher.reset();
					}

					derivedKey.concat(block);
				}
				derivedKey.sigBytes = keySize * 4;

				return derivedKey;
			}
		});

		/**
		 * Derives a key from a password.
		 *
		 * @param {WordArray|string} password The password.
		 * @param {WordArray|string} salt A salt.
		 * @param {Object} cfg (Optional) The configuration options to use for this computation.
		 *
		 * @return {WordArray} The derived key.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var key = CryptoJS.EvpKDF(password, salt);
		 *     var key = CryptoJS.EvpKDF(password, salt, { keySize: 8 });
		 *     var key = CryptoJS.EvpKDF(password, salt, { keySize: 8, iterations: 1000 });
		 */
		C.EvpKDF = function (password, salt, cfg) {
			return EvpKDF.create(cfg).compute(password, salt);
		};
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var C_algo = C.algo;
		var SHA256 = C_algo.SHA256;

		/**
		 * SHA-224 hash algorithm.
		 */
		var SHA224 = C_algo.SHA224 = SHA256.extend({
			_doReset: function () {
				this._hash = new WordArray.init([
					0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
					0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4
				]);
			},

			_doFinalize: function () {
				var hash = SHA256._doFinalize.call(this);

				hash.sigBytes -= 4;

				return hash;
			}
		});

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.SHA224('message');
		 *     var hash = CryptoJS.SHA224(wordArray);
		 */
		C.SHA224 = SHA256._createHelper(SHA224);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacSHA224(message, key);
		 */
		C.HmacSHA224 = SHA256._createHmacHelper(SHA224);
	}());


	(function (undefined) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var Base = C_lib.Base;
		var X32WordArray = C_lib.WordArray;

		/**
		 * x64 namespace.
		 */
		var C_x64 = C.x64 = {};

		/**
		 * A 64-bit word.
		 */
		var X64Word = C_x64.Word = Base.extend({
			/**
			 * Initializes a newly created 64-bit word.
			 *
			 * @param {number} high The high 32 bits.
			 * @param {number} low The low 32 bits.
			 *
			 * @example
			 *
			 *     var x64Word = CryptoJS.x64.Word.create(0x00010203, 0x04050607);
			 */
			init: function (high, low) {
				this.high = high;
				this.low = low;
			}

			/**
			 * Bitwise NOTs this word.
			 *
			 * @return {X64Word} A new x64-Word object after negating.
			 *
			 * @example
			 *
			 *     var negated = x64Word.not();
			 */
			// not: function () {
			// var high = ~this.high;
			// var low = ~this.low;

			// return X64Word.create(high, low);
			// },

			/**
			 * Bitwise ANDs this word with the passed word.
			 *
			 * @param {X64Word} word The x64-Word to AND with this word.
			 *
			 * @return {X64Word} A new x64-Word object after ANDing.
			 *
			 * @example
			 *
			 *     var anded = x64Word.and(anotherX64Word);
			 */
			// and: function (word) {
			// var high = this.high & word.high;
			// var low = this.low & word.low;

			// return X64Word.create(high, low);
			// },

			/**
			 * Bitwise ORs this word with the passed word.
			 *
			 * @param {X64Word} word The x64-Word to OR with this word.
			 *
			 * @return {X64Word} A new x64-Word object after ORing.
			 *
			 * @example
			 *
			 *     var ored = x64Word.or(anotherX64Word);
			 */
			// or: function (word) {
			// var high = this.high | word.high;
			// var low = this.low | word.low;

			// return X64Word.create(high, low);
			// },

			/**
			 * Bitwise XORs this word with the passed word.
			 *
			 * @param {X64Word} word The x64-Word to XOR with this word.
			 *
			 * @return {X64Word} A new x64-Word object after XORing.
			 *
			 * @example
			 *
			 *     var xored = x64Word.xor(anotherX64Word);
			 */
			// xor: function (word) {
			// var high = this.high ^ word.high;
			// var low = this.low ^ word.low;

			// return X64Word.create(high, low);
			// },

			/**
			 * Shifts this word n bits to the left.
			 *
			 * @param {number} n The number of bits to shift.
			 *
			 * @return {X64Word} A new x64-Word object after shifting.
			 *
			 * @example
			 *
			 *     var shifted = x64Word.shiftL(25);
			 */
			// shiftL: function (n) {
			// if (n < 32) {
			// var high = (this.high << n) | (this.low >>> (32 - n));
			// var low = this.low << n;
			// } else {
			// var high = this.low << (n - 32);
			// var low = 0;
			// }

			// return X64Word.create(high, low);
			// },

			/**
			 * Shifts this word n bits to the right.
			 *
			 * @param {number} n The number of bits to shift.
			 *
			 * @return {X64Word} A new x64-Word object after shifting.
			 *
			 * @example
			 *
			 *     var shifted = x64Word.shiftR(7);
			 */
			// shiftR: function (n) {
			// if (n < 32) {
			// var low = (this.low >>> n) | (this.high << (32 - n));
			// var high = this.high >>> n;
			// } else {
			// var low = this.high >>> (n - 32);
			// var high = 0;
			// }

			// return X64Word.create(high, low);
			// },

			/**
			 * Rotates this word n bits to the left.
			 *
			 * @param {number} n The number of bits to rotate.
			 *
			 * @return {X64Word} A new x64-Word object after rotating.
			 *
			 * @example
			 *
			 *     var rotated = x64Word.rotL(25);
			 */
			// rotL: function (n) {
			// return this.shiftL(n).or(this.shiftR(64 - n));
			// },

			/**
			 * Rotates this word n bits to the right.
			 *
			 * @param {number} n The number of bits to rotate.
			 *
			 * @return {X64Word} A new x64-Word object after rotating.
			 *
			 * @example
			 *
			 *     var rotated = x64Word.rotR(7);
			 */
			// rotR: function (n) {
			// return this.shiftR(n).or(this.shiftL(64 - n));
			// },

			/**
			 * Adds this word with the passed word.
			 *
			 * @param {X64Word} word The x64-Word to add with this word.
			 *
			 * @return {X64Word} A new x64-Word object after adding.
			 *
			 * @example
			 *
			 *     var added = x64Word.add(anotherX64Word);
			 */
			// add: function (word) {
			// var low = (this.low + word.low) | 0;
			// var carry = (low >>> 0) < (this.low >>> 0) ? 1 : 0;
			// var high = (this.high + word.high + carry) | 0;

			// return X64Word.create(high, low);
			// }
		});

		/**
		 * An array of 64-bit words.
		 *
		 * @property {Array} words The array of CryptoJS.x64.Word objects.
		 * @property {number} sigBytes The number of significant bytes in this word array.
		 */
		var X64WordArray = C_x64.WordArray = Base.extend({
			/**
			 * Initializes a newly created word array.
			 *
			 * @param {Array} words (Optional) An array of CryptoJS.x64.Word objects.
			 * @param {number} sigBytes (Optional) The number of significant bytes in the words.
			 *
			 * @example
			 *
			 *     var wordArray = CryptoJS.x64.WordArray.create();
			 *
			 *     var wordArray = CryptoJS.x64.WordArray.create([
			 *         CryptoJS.x64.Word.create(0x00010203, 0x04050607),
			 *         CryptoJS.x64.Word.create(0x18191a1b, 0x1c1d1e1f)
			 *     ]);
			 *
			 *     var wordArray = CryptoJS.x64.WordArray.create([
			 *         CryptoJS.x64.Word.create(0x00010203, 0x04050607),
			 *         CryptoJS.x64.Word.create(0x18191a1b, 0x1c1d1e1f)
			 *     ], 10);
			 */
			init: function (words, sigBytes) {
				words = this.words = words || [];

				if (sigBytes != undefined) {
					this.sigBytes = sigBytes;
				} else {
					this.sigBytes = words.length * 8;
				}
			},

			/**
			 * Converts this 64-bit word array to a 32-bit word array.
			 *
			 * @return {CryptoJS.lib.WordArray} This word array's data as a 32-bit word array.
			 *
			 * @example
			 *
			 *     var x32WordArray = x64WordArray.toX32();
			 */
			toX32: function () {
				// Shortcuts
				var x64Words = this.words;
				var x64WordsLength = x64Words.length;

				// Convert
				var x32Words = [];
				for (var i = 0; i < x64WordsLength; i++) {
					var x64Word = x64Words[i];
					x32Words.push(x64Word.high);
					x32Words.push(x64Word.low);
				}

				return X32WordArray.create(x32Words, this.sigBytes);
			},

			/**
			 * Creates a copy of this word array.
			 *
			 * @return {X64WordArray} The clone.
			 *
			 * @example
			 *
			 *     var clone = x64WordArray.clone();
			 */
			clone: function () {
				var clone = Base.clone.call(this);

				// Clone "words" array
				var words = clone.words = this.words.slice(0);

				// Clone each X64Word object
				var wordsLength = words.length;
				for (var i = 0; i < wordsLength; i++) {
					words[i] = words[i].clone();
				}

				return clone;
			}
		});
	}());


	(function (Math) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var Hasher = C_lib.Hasher;
		var C_x64 = C.x64;
		var X64Word = C_x64.Word;
		var C_algo = C.algo;

		// Constants tables
		var RHO_OFFSETS = [];
		var PI_INDEXES = [];
		var ROUND_CONSTANTS = [];

		// Compute Constants
		(function () {
			// Compute rho offset constants
			var x = 1, y = 0;
			for (var t = 0; t < 24; t++) {
				RHO_OFFSETS[x + 5 * y] = ((t + 1) * (t + 2) / 2) % 64;

				var newX = y % 5;
				var newY = (2 * x + 3 * y) % 5;
				x = newX;
				y = newY;
			}

			// Compute pi index constants
			for (var x = 0; x < 5; x++) {
				for (var y = 0; y < 5; y++) {
					PI_INDEXES[x + 5 * y] = y + ((2 * x + 3 * y) % 5) * 5;
				}
			}

			// Compute round constants
			var LFSR = 0x01;
			for (var i = 0; i < 24; i++) {
				var roundConstantMsw = 0;
				var roundConstantLsw = 0;

				for (var j = 0; j < 7; j++) {
					if (LFSR & 0x01) {
						var bitPosition = (1 << j) - 1;
						if (bitPosition < 32) {
							roundConstantLsw ^= 1 << bitPosition;
						} else /* if (bitPosition >= 32) */ {
							roundConstantMsw ^= 1 << (bitPosition - 32);
						}
					}

					// Compute next LFSR
					if (LFSR & 0x80) {
						// Primitive polynomial over GF(2): x^8 + x^6 + x^5 + x^4 + 1
						LFSR = (LFSR << 1) ^ 0x71;
					} else {
						LFSR <<= 1;
					}
				}

				ROUND_CONSTANTS[i] = X64Word.create(roundConstantMsw, roundConstantLsw);
			}
		}());

		// Reusable objects for temporary values
		var T = [];
		(function () {
			for (var i = 0; i < 25; i++) {
				T[i] = X64Word.create();
			}
		}());

		/**
		 * SHA-3 hash algorithm.
		 */
		var SHA3 = C_algo.SHA3 = Hasher.extend({
			/**
			 * Configuration options.
			 *
			 * @property {number} outputLength
			 *   The desired number of bits in the output hash.
			 *   Only values permitted are: 224, 256, 384, 512.
			 *   Default: 512
			 */
			cfg: Hasher.cfg.extend({
				outputLength: 512
			}),

			_doReset: function () {
				var state = this._state = []
				for (var i = 0; i < 25; i++) {
					state[i] = new X64Word.init();
				}

				this.blockSize = (1600 - 2 * this.cfg.outputLength) / 32;
			},

			_doProcessBlock: function (M, offset) {
				// Shortcuts
				var state = this._state;
				var nBlockSizeLanes = this.blockSize / 2;

				// Absorb
				for (var i = 0; i < nBlockSizeLanes; i++) {
					// Shortcuts
					var M2i = M[offset + 2 * i];
					var M2i1 = M[offset + 2 * i + 1];

					// Swap endian
					M2i = (
						(((M2i << 8) | (M2i >>> 24)) & 0x00ff00ff) |
						(((M2i << 24) | (M2i >>> 8)) & 0xff00ff00)
					);
					M2i1 = (
						(((M2i1 << 8) | (M2i1 >>> 24)) & 0x00ff00ff) |
						(((M2i1 << 24) | (M2i1 >>> 8)) & 0xff00ff00)
					);

					// Absorb message into state
					var lane = state[i];
					lane.high ^= M2i1;
					lane.low ^= M2i;
				}

				// Rounds
				for (var round = 0; round < 24; round++) {
					// Theta
					for (var x = 0; x < 5; x++) {
						// Mix column lanes
						var tMsw = 0, tLsw = 0;
						for (var y = 0; y < 5; y++) {
							var lane = state[x + 5 * y];
							tMsw ^= lane.high;
							tLsw ^= lane.low;
						}

						// Temporary values
						var Tx = T[x];
						Tx.high = tMsw;
						Tx.low = tLsw;
					}
					for (var x = 0; x < 5; x++) {
						// Shortcuts
						var Tx4 = T[(x + 4) % 5];
						var Tx1 = T[(x + 1) % 5];
						var Tx1Msw = Tx1.high;
						var Tx1Lsw = Tx1.low;

						// Mix surrounding columns
						var tMsw = Tx4.high ^ ((Tx1Msw << 1) | (Tx1Lsw >>> 31));
						var tLsw = Tx4.low ^ ((Tx1Lsw << 1) | (Tx1Msw >>> 31));
						for (var y = 0; y < 5; y++) {
							var lane = state[x + 5 * y];
							lane.high ^= tMsw;
							lane.low ^= tLsw;
						}
					}

					// Rho Pi
					for (var laneIndex = 1; laneIndex < 25; laneIndex++) {
						var tMsw;
						var tLsw;

						// Shortcuts
						var lane = state[laneIndex];
						var laneMsw = lane.high;
						var laneLsw = lane.low;
						var rhoOffset = RHO_OFFSETS[laneIndex];

						// Rotate lanes
						if (rhoOffset < 32) {
							tMsw = (laneMsw << rhoOffset) | (laneLsw >>> (32 - rhoOffset));
							tLsw = (laneLsw << rhoOffset) | (laneMsw >>> (32 - rhoOffset));
						} else /* if (rhoOffset >= 32) */ {
							tMsw = (laneLsw << (rhoOffset - 32)) | (laneMsw >>> (64 - rhoOffset));
							tLsw = (laneMsw << (rhoOffset - 32)) | (laneLsw >>> (64 - rhoOffset));
						}

						// Transpose lanes
						var TPiLane = T[PI_INDEXES[laneIndex]];
						TPiLane.high = tMsw;
						TPiLane.low = tLsw;
					}

					// Rho pi at x = y = 0
					var T0 = T[0];
					var state0 = state[0];
					T0.high = state0.high;
					T0.low = state0.low;

					// Chi
					for (var x = 0; x < 5; x++) {
						for (var y = 0; y < 5; y++) {
							// Shortcuts
							var laneIndex = x + 5 * y;
							var lane = state[laneIndex];
							var TLane = T[laneIndex];
							var Tx1Lane = T[((x + 1) % 5) + 5 * y];
							var Tx2Lane = T[((x + 2) % 5) + 5 * y];

							// Mix rows
							lane.high = TLane.high ^ (~Tx1Lane.high & Tx2Lane.high);
							lane.low = TLane.low ^ (~Tx1Lane.low & Tx2Lane.low);
						}
					}

					// Iota
					var lane = state[0];
					var roundConstant = ROUND_CONSTANTS[round];
					lane.high ^= roundConstant.high;
					lane.low ^= roundConstant.low;
				}
			},

			_doFinalize: function () {
				// Shortcuts
				var data = this._data;
				var dataWords = data.words;
				var nBitsTotal = this._nDataBytes * 8;
				var nBitsLeft = data.sigBytes * 8;
				var blockSizeBits = this.blockSize * 32;

				// Add padding
				dataWords[nBitsLeft >>> 5] |= 0x1 << (24 - nBitsLeft % 32);
				dataWords[((Math.ceil((nBitsLeft + 1) / blockSizeBits) * blockSizeBits) >>> 5) - 1] |= 0x80;
				data.sigBytes = dataWords.length * 4;

				// Hash final blocks
				this._process();

				// Shortcuts
				var state = this._state;
				var outputLengthBytes = this.cfg.outputLength / 8;
				var outputLengthLanes = outputLengthBytes / 8;

				// Squeeze
				var hashWords = [];
				for (var i = 0; i < outputLengthLanes; i++) {
					// Shortcuts
					var lane = state[i];
					var laneMsw = lane.high;
					var laneLsw = lane.low;

					// Swap endian
					laneMsw = (
						(((laneMsw << 8) | (laneMsw >>> 24)) & 0x00ff00ff) |
						(((laneMsw << 24) | (laneMsw >>> 8)) & 0xff00ff00)
					);
					laneLsw = (
						(((laneLsw << 8) | (laneLsw >>> 24)) & 0x00ff00ff) |
						(((laneLsw << 24) | (laneLsw >>> 8)) & 0xff00ff00)
					);

					// Squeeze state to retrieve hash
					hashWords.push(laneLsw);
					hashWords.push(laneMsw);
				}

				// Return final computed hash
				return new WordArray.init(hashWords, outputLengthBytes);
			},

			clone: function () {
				var clone = Hasher.clone.call(this);

				var state = clone._state = this._state.slice(0);
				for (var i = 0; i < 25; i++) {
					state[i] = state[i].clone();
				}

				return clone;
			}
		});

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.SHA3('message');
		 *     var hash = CryptoJS.SHA3(wordArray);
		 */
		C.SHA3 = Hasher._createHelper(SHA3);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacSHA3(message, key);
		 */
		C.HmacSHA3 = Hasher._createHmacHelper(SHA3);
	}(Math));


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var Hasher = C_lib.Hasher;
		var C_x64 = C.x64;
		var X64Word = C_x64.Word;
		var X64WordArray = C_x64.WordArray;
		var C_algo = C.algo;

		function X64Word_create() {
			return X64Word.create.apply(X64Word, arguments);
		}

		// Constants
		var K = [
			X64Word_create(0x428a2f98, 0xd728ae22), X64Word_create(0x71374491, 0x23ef65cd),
			X64Word_create(0xb5c0fbcf, 0xec4d3b2f), X64Word_create(0xe9b5dba5, 0x8189dbbc),
			X64Word_create(0x3956c25b, 0xf348b538), X64Word_create(0x59f111f1, 0xb605d019),
			X64Word_create(0x923f82a4, 0xaf194f9b), X64Word_create(0xab1c5ed5, 0xda6d8118),
			X64Word_create(0xd807aa98, 0xa3030242), X64Word_create(0x12835b01, 0x45706fbe),
			X64Word_create(0x243185be, 0x4ee4b28c), X64Word_create(0x550c7dc3, 0xd5ffb4e2),
			X64Word_create(0x72be5d74, 0xf27b896f), X64Word_create(0x80deb1fe, 0x3b1696b1),
			X64Word_create(0x9bdc06a7, 0x25c71235), X64Word_create(0xc19bf174, 0xcf692694),
			X64Word_create(0xe49b69c1, 0x9ef14ad2), X64Word_create(0xefbe4786, 0x384f25e3),
			X64Word_create(0x0fc19dc6, 0x8b8cd5b5), X64Word_create(0x240ca1cc, 0x77ac9c65),
			X64Word_create(0x2de92c6f, 0x592b0275), X64Word_create(0x4a7484aa, 0x6ea6e483),
			X64Word_create(0x5cb0a9dc, 0xbd41fbd4), X64Word_create(0x76f988da, 0x831153b5),
			X64Word_create(0x983e5152, 0xee66dfab), X64Word_create(0xa831c66d, 0x2db43210),
			X64Word_create(0xb00327c8, 0x98fb213f), X64Word_create(0xbf597fc7, 0xbeef0ee4),
			X64Word_create(0xc6e00bf3, 0x3da88fc2), X64Word_create(0xd5a79147, 0x930aa725),
			X64Word_create(0x06ca6351, 0xe003826f), X64Word_create(0x14292967, 0x0a0e6e70),
			X64Word_create(0x27b70a85, 0x46d22ffc), X64Word_create(0x2e1b2138, 0x5c26c926),
			X64Word_create(0x4d2c6dfc, 0x5ac42aed), X64Word_create(0x53380d13, 0x9d95b3df),
			X64Word_create(0x650a7354, 0x8baf63de), X64Word_create(0x766a0abb, 0x3c77b2a8),
			X64Word_create(0x81c2c92e, 0x47edaee6), X64Word_create(0x92722c85, 0x1482353b),
			X64Word_create(0xa2bfe8a1, 0x4cf10364), X64Word_create(0xa81a664b, 0xbc423001),
			X64Word_create(0xc24b8b70, 0xd0f89791), X64Word_create(0xc76c51a3, 0x0654be30),
			X64Word_create(0xd192e819, 0xd6ef5218), X64Word_create(0xd6990624, 0x5565a910),
			X64Word_create(0xf40e3585, 0x5771202a), X64Word_create(0x106aa070, 0x32bbd1b8),
			X64Word_create(0x19a4c116, 0xb8d2d0c8), X64Word_create(0x1e376c08, 0x5141ab53),
			X64Word_create(0x2748774c, 0xdf8eeb99), X64Word_create(0x34b0bcb5, 0xe19b48a8),
			X64Word_create(0x391c0cb3, 0xc5c95a63), X64Word_create(0x4ed8aa4a, 0xe3418acb),
			X64Word_create(0x5b9cca4f, 0x7763e373), X64Word_create(0x682e6ff3, 0xd6b2b8a3),
			X64Word_create(0x748f82ee, 0x5defb2fc), X64Word_create(0x78a5636f, 0x43172f60),
			X64Word_create(0x84c87814, 0xa1f0ab72), X64Word_create(0x8cc70208, 0x1a6439ec),
			X64Word_create(0x90befffa, 0x23631e28), X64Word_create(0xa4506ceb, 0xde82bde9),
			X64Word_create(0xbef9a3f7, 0xb2c67915), X64Word_create(0xc67178f2, 0xe372532b),
			X64Word_create(0xca273ece, 0xea26619c), X64Word_create(0xd186b8c7, 0x21c0c207),
			X64Word_create(0xeada7dd6, 0xcde0eb1e), X64Word_create(0xf57d4f7f, 0xee6ed178),
			X64Word_create(0x06f067aa, 0x72176fba), X64Word_create(0x0a637dc5, 0xa2c898a6),
			X64Word_create(0x113f9804, 0xbef90dae), X64Word_create(0x1b710b35, 0x131c471b),
			X64Word_create(0x28db77f5, 0x23047d84), X64Word_create(0x32caab7b, 0x40c72493),
			X64Word_create(0x3c9ebe0a, 0x15c9bebc), X64Word_create(0x431d67c4, 0x9c100d4c),
			X64Word_create(0x4cc5d4be, 0xcb3e42b6), X64Word_create(0x597f299c, 0xfc657e2a),
			X64Word_create(0x5fcb6fab, 0x3ad6faec), X64Word_create(0x6c44198c, 0x4a475817)
		];

		// Reusable objects
		var W = [];
		(function () {
			for (var i = 0; i < 80; i++) {
				W[i] = X64Word_create();
			}
		}());

		/**
		 * SHA-512 hash algorithm.
		 */
		var SHA512 = C_algo.SHA512 = Hasher.extend({
			_doReset: function () {
				this._hash = new X64WordArray.init([
					new X64Word.init(0x6a09e667, 0xf3bcc908), new X64Word.init(0xbb67ae85, 0x84caa73b),
					new X64Word.init(0x3c6ef372, 0xfe94f82b), new X64Word.init(0xa54ff53a, 0x5f1d36f1),
					new X64Word.init(0x510e527f, 0xade682d1), new X64Word.init(0x9b05688c, 0x2b3e6c1f),
					new X64Word.init(0x1f83d9ab, 0xfb41bd6b), new X64Word.init(0x5be0cd19, 0x137e2179)
				]);
			},

			_doProcessBlock: function (M, offset) {
				// Shortcuts
				var H = this._hash.words;

				var H0 = H[0];
				var H1 = H[1];
				var H2 = H[2];
				var H3 = H[3];
				var H4 = H[4];
				var H5 = H[5];
				var H6 = H[6];
				var H7 = H[7];

				var H0h = H0.high;
				var H0l = H0.low;
				var H1h = H1.high;
				var H1l = H1.low;
				var H2h = H2.high;
				var H2l = H2.low;
				var H3h = H3.high;
				var H3l = H3.low;
				var H4h = H4.high;
				var H4l = H4.low;
				var H5h = H5.high;
				var H5l = H5.low;
				var H6h = H6.high;
				var H6l = H6.low;
				var H7h = H7.high;
				var H7l = H7.low;

				// Working variables
				var ah = H0h;
				var al = H0l;
				var bh = H1h;
				var bl = H1l;
				var ch = H2h;
				var cl = H2l;
				var dh = H3h;
				var dl = H3l;
				var eh = H4h;
				var el = H4l;
				var fh = H5h;
				var fl = H5l;
				var gh = H6h;
				var gl = H6l;
				var hh = H7h;
				var hl = H7l;

				// Rounds
				for (var i = 0; i < 80; i++) {
					var Wil;
					var Wih;

					// Shortcut
					var Wi = W[i];

					// Extend message
					if (i < 16) {
						Wih = Wi.high = M[offset + i * 2] | 0;
						Wil = Wi.low = M[offset + i * 2 + 1] | 0;
					} else {
						// Gamma0
						var gamma0x = W[i - 15];
						var gamma0xh = gamma0x.high;
						var gamma0xl = gamma0x.low;
						var gamma0h = ((gamma0xh >>> 1) | (gamma0xl << 31)) ^ ((gamma0xh >>> 8) | (gamma0xl << 24)) ^ (gamma0xh >>> 7);
						var gamma0l = ((gamma0xl >>> 1) | (gamma0xh << 31)) ^ ((gamma0xl >>> 8) | (gamma0xh << 24)) ^ ((gamma0xl >>> 7) | (gamma0xh << 25));

						// Gamma1
						var gamma1x = W[i - 2];
						var gamma1xh = gamma1x.high;
						var gamma1xl = gamma1x.low;
						var gamma1h = ((gamma1xh >>> 19) | (gamma1xl << 13)) ^ ((gamma1xh << 3) | (gamma1xl >>> 29)) ^ (gamma1xh >>> 6);
						var gamma1l = ((gamma1xl >>> 19) | (gamma1xh << 13)) ^ ((gamma1xl << 3) | (gamma1xh >>> 29)) ^ ((gamma1xl >>> 6) | (gamma1xh << 26));

						// W[i] = gamma0 + W[i - 7] + gamma1 + W[i - 16]
						var Wi7 = W[i - 7];
						var Wi7h = Wi7.high;
						var Wi7l = Wi7.low;

						var Wi16 = W[i - 16];
						var Wi16h = Wi16.high;
						var Wi16l = Wi16.low;

						Wil = gamma0l + Wi7l;
						Wih = gamma0h + Wi7h + ((Wil >>> 0) < (gamma0l >>> 0) ? 1 : 0);
						Wil = Wil + gamma1l;
						Wih = Wih + gamma1h + ((Wil >>> 0) < (gamma1l >>> 0) ? 1 : 0);
						Wil = Wil + Wi16l;
						Wih = Wih + Wi16h + ((Wil >>> 0) < (Wi16l >>> 0) ? 1 : 0);

						Wi.high = Wih;
						Wi.low = Wil;
					}

					var chh = (eh & fh) ^ (~eh & gh);
					var chl = (el & fl) ^ (~el & gl);
					var majh = (ah & bh) ^ (ah & ch) ^ (bh & ch);
					var majl = (al & bl) ^ (al & cl) ^ (bl & cl);

					var sigma0h = ((ah >>> 28) | (al << 4)) ^ ((ah << 30) | (al >>> 2)) ^ ((ah << 25) | (al >>> 7));
					var sigma0l = ((al >>> 28) | (ah << 4)) ^ ((al << 30) | (ah >>> 2)) ^ ((al << 25) | (ah >>> 7));
					var sigma1h = ((eh >>> 14) | (el << 18)) ^ ((eh >>> 18) | (el << 14)) ^ ((eh << 23) | (el >>> 9));
					var sigma1l = ((el >>> 14) | (eh << 18)) ^ ((el >>> 18) | (eh << 14)) ^ ((el << 23) | (eh >>> 9));

					// t1 = h + sigma1 + ch + K[i] + W[i]
					var Ki = K[i];
					var Kih = Ki.high;
					var Kil = Ki.low;

					var t1l = hl + sigma1l;
					var t1h = hh + sigma1h + ((t1l >>> 0) < (hl >>> 0) ? 1 : 0);
					var t1l = t1l + chl;
					var t1h = t1h + chh + ((t1l >>> 0) < (chl >>> 0) ? 1 : 0);
					var t1l = t1l + Kil;
					var t1h = t1h + Kih + ((t1l >>> 0) < (Kil >>> 0) ? 1 : 0);
					var t1l = t1l + Wil;
					var t1h = t1h + Wih + ((t1l >>> 0) < (Wil >>> 0) ? 1 : 0);

					// t2 = sigma0 + maj
					var t2l = sigma0l + majl;
					var t2h = sigma0h + majh + ((t2l >>> 0) < (sigma0l >>> 0) ? 1 : 0);

					// Update working variables
					hh = gh;
					hl = gl;
					gh = fh;
					gl = fl;
					fh = eh;
					fl = el;
					el = (dl + t1l) | 0;
					eh = (dh + t1h + ((el >>> 0) < (dl >>> 0) ? 1 : 0)) | 0;
					dh = ch;
					dl = cl;
					ch = bh;
					cl = bl;
					bh = ah;
					bl = al;
					al = (t1l + t2l) | 0;
					ah = (t1h + t2h + ((al >>> 0) < (t1l >>> 0) ? 1 : 0)) | 0;
				}

				// Intermediate hash value
				H0l = H0.low = (H0l + al);
				H0.high = (H0h + ah + ((H0l >>> 0) < (al >>> 0) ? 1 : 0));
				H1l = H1.low = (H1l + bl);
				H1.high = (H1h + bh + ((H1l >>> 0) < (bl >>> 0) ? 1 : 0));
				H2l = H2.low = (H2l + cl);
				H2.high = (H2h + ch + ((H2l >>> 0) < (cl >>> 0) ? 1 : 0));
				H3l = H3.low = (H3l + dl);
				H3.high = (H3h + dh + ((H3l >>> 0) < (dl >>> 0) ? 1 : 0));
				H4l = H4.low = (H4l + el);
				H4.high = (H4h + eh + ((H4l >>> 0) < (el >>> 0) ? 1 : 0));
				H5l = H5.low = (H5l + fl);
				H5.high = (H5h + fh + ((H5l >>> 0) < (fl >>> 0) ? 1 : 0));
				H6l = H6.low = (H6l + gl);
				H6.high = (H6h + gh + ((H6l >>> 0) < (gl >>> 0) ? 1 : 0));
				H7l = H7.low = (H7l + hl);
				H7.high = (H7h + hh + ((H7l >>> 0) < (hl >>> 0) ? 1 : 0));
			},

			_doFinalize: function () {
				// Shortcuts
				var data = this._data;
				var dataWords = data.words;

				var nBitsTotal = this._nDataBytes * 8;
				var nBitsLeft = data.sigBytes * 8;

				// Add padding
				dataWords[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);
				dataWords[(((nBitsLeft + 128) >>> 10) << 5) + 30] = Math.floor(nBitsTotal / 0x100000000);
				dataWords[(((nBitsLeft + 128) >>> 10) << 5) + 31] = nBitsTotal;
				data.sigBytes = dataWords.length * 4;

				// Hash final blocks
				this._process();

				// Convert hash to 32-bit word array before returning
				var hash = this._hash.toX32();

				// Return final computed hash
				return hash;
			},

			clone: function () {
				var clone = Hasher.clone.call(this);
				clone._hash = this._hash.clone();

				return clone;
			},

			blockSize: 1024 / 32
		});

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.SHA512('message');
		 *     var hash = CryptoJS.SHA512(wordArray);
		 */
		C.SHA512 = Hasher._createHelper(SHA512);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacSHA512(message, key);
		 */
		C.HmacSHA512 = Hasher._createHmacHelper(SHA512);
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_x64 = C.x64;
		var X64Word = C_x64.Word;
		var X64WordArray = C_x64.WordArray;
		var C_algo = C.algo;
		var SHA512 = C_algo.SHA512;

		/**
		 * SHA-384 hash algorithm.
		 */
		var SHA384 = C_algo.SHA384 = SHA512.extend({
			_doReset: function () {
				this._hash = new X64WordArray.init([
					new X64Word.init(0xcbbb9d5d, 0xc1059ed8), new X64Word.init(0x629a292a, 0x367cd507),
					new X64Word.init(0x9159015a, 0x3070dd17), new X64Word.init(0x152fecd8, 0xf70e5939),
					new X64Word.init(0x67332667, 0xffc00b31), new X64Word.init(0x8eb44a87, 0x68581511),
					new X64Word.init(0xdb0c2e0d, 0x64f98fa7), new X64Word.init(0x47b5481d, 0xbefa4fa4)
				]);
			},

			_doFinalize: function () {
				var hash = SHA512._doFinalize.call(this);

				hash.sigBytes -= 16;

				return hash;
			}
		});

		/**
		 * Shortcut function to the hasher's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 *
		 * @return {WordArray} The hash.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hash = CryptoJS.SHA384('message');
		 *     var hash = CryptoJS.SHA384(wordArray);
		 */
		C.SHA384 = SHA512._createHelper(SHA384);

		/**
		 * Shortcut function to the HMAC's object interface.
		 *
		 * @param {WordArray|string} message The message to hash.
		 * @param {WordArray|string} key The secret key.
		 *
		 * @return {WordArray} The HMAC.
		 *
		 * @static
		 *
		 * @example
		 *
		 *     var hmac = CryptoJS.HmacSHA384(message, key);
		 */
		C.HmacSHA384 = SHA512._createHmacHelper(SHA384);
	}());


	/**
	 * Cipher core components.
	 */
	CryptoJS.lib.Cipher || (function (undefined) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var Base = C_lib.Base;
		var WordArray = C_lib.WordArray;
		var BufferedBlockAlgorithm = C_lib.BufferedBlockAlgorithm;
		var C_enc = C.enc;
		var Utf8 = C_enc.Utf8;
		var Base64 = C_enc.Base64;
		var C_algo = C.algo;
		var EvpKDF = C_algo.EvpKDF;

		/**
		 * Abstract base cipher template.
		 *
		 * @property {number} keySize This cipher's key size. Default: 4 (128 bits)
		 * @property {number} ivSize This cipher's IV size. Default: 4 (128 bits)
		 * @property {number} _ENC_XFORM_MODE A constant representing encryption mode.
		 * @property {number} _DEC_XFORM_MODE A constant representing decryption mode.
		 */
		var Cipher = C_lib.Cipher = BufferedBlockAlgorithm.extend({
			/**
			 * Configuration options.
			 *
			 * @property {WordArray} iv The IV to use for this operation.
			 */
			cfg: Base.extend(),

			/**
			 * Creates this cipher in encryption mode.
			 *
			 * @param {WordArray} key The key.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @return {Cipher} A cipher instance.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var cipher = CryptoJS.algo.AES.createEncryptor(keyWordArray, { iv: ivWordArray });
			 */
			createEncryptor: function (key, cfg) {
				return this.create(this._ENC_XFORM_MODE, key, cfg);
			},

			/**
			 * Creates this cipher in decryption mode.
			 *
			 * @param {WordArray} key The key.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @return {Cipher} A cipher instance.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var cipher = CryptoJS.algo.AES.createDecryptor(keyWordArray, { iv: ivWordArray });
			 */
			createDecryptor: function (key, cfg) {
				return this.create(this._DEC_XFORM_MODE, key, cfg);
			},

			/**
			 * Initializes a newly created cipher.
			 *
			 * @param {number} xformMode Either the encryption or decryption transormation mode constant.
			 * @param {WordArray} key The key.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @example
			 *
			 *     var cipher = CryptoJS.algo.AES.create(CryptoJS.algo.AES._ENC_XFORM_MODE, keyWordArray, { iv: ivWordArray });
			 */
			init: function (xformMode, key, cfg) {
				// Apply config defaults
				this.cfg = this.cfg.extend(cfg);

				// Store transform mode and key
				this._xformMode = xformMode;
				this._key = key;

				// Set initial values
				this.reset();
			},

			/**
			 * Resets this cipher to its initial state.
			 *
			 * @example
			 *
			 *     cipher.reset();
			 */
			reset: function () {
				// Reset data buffer
				BufferedBlockAlgorithm.reset.call(this);

				// Perform concrete-cipher logic
				this._doReset();
			},

			/**
			 * Adds data to be encrypted or decrypted.
			 *
			 * @param {WordArray|string} dataUpdate The data to encrypt or decrypt.
			 *
			 * @return {WordArray} The data after processing.
			 *
			 * @example
			 *
			 *     var encrypted = cipher.process('data');
			 *     var encrypted = cipher.process(wordArray);
			 */
			process: function (dataUpdate) {
				// Append
				this._append(dataUpdate);

				// Process available blocks
				return this._process();
			},

			/**
			 * Finalizes the encryption or decryption process.
			 * Note that the finalize operation is effectively a destructive, read-once operation.
			 *
			 * @param {WordArray|string} dataUpdate The final data to encrypt or decrypt.
			 *
			 * @return {WordArray} The data after final processing.
			 *
			 * @example
			 *
			 *     var encrypted = cipher.finalize();
			 *     var encrypted = cipher.finalize('data');
			 *     var encrypted = cipher.finalize(wordArray);
			 */
			finalize: function (dataUpdate) {
				// Final data update
				if (dataUpdate) {
					this._append(dataUpdate);
				}

				// Perform concrete-cipher logic
				var finalProcessedData = this._doFinalize();

				return finalProcessedData;
			},

			keySize: 128 / 32,

			ivSize: 128 / 32,

			_ENC_XFORM_MODE: 1,

			_DEC_XFORM_MODE: 2,

			/**
			 * Creates shortcut functions to a cipher's object interface.
			 *
			 * @param {Cipher} cipher The cipher to create a helper for.
			 *
			 * @return {Object} An object with encrypt and decrypt shortcut functions.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var AES = CryptoJS.lib.Cipher._createHelper(CryptoJS.algo.AES);
			 */
			_createHelper: (function () {
				function selectCipherStrategy(key) {
					if (typeof key == 'string') {
						return PasswordBasedCipher;
					} else {
						return SerializableCipher;
					}
				}

				return function (cipher) {
					return {
						encrypt: function (message, key, cfg) {
							return selectCipherStrategy(key).encrypt(cipher, message, key, cfg);
						},

						decrypt: function (ciphertext, key, cfg) {
							return selectCipherStrategy(key).decrypt(cipher, ciphertext, key, cfg);
						}
					};
				};
			}())
		});

		/**
		 * Abstract base stream cipher template.
		 *
		 * @property {number} blockSize The number of 32-bit words this cipher operates on. Default: 1 (32 bits)
		 */
		var StreamCipher = C_lib.StreamCipher = Cipher.extend({
			_doFinalize: function () {
				// Process partial blocks
				var finalProcessedBlocks = this._process(!!'flush');

				return finalProcessedBlocks;
			},

			blockSize: 1
		});

		/**
		 * Mode namespace.
		 */
		var C_mode = C.mode = {};

		/**
		 * Abstract base block cipher mode template.
		 */
		var BlockCipherMode = C_lib.BlockCipherMode = Base.extend({
			/**
			 * Creates this mode for encryption.
			 *
			 * @param {Cipher} cipher A block cipher instance.
			 * @param {Array} iv The IV words.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var mode = CryptoJS.mode.CBC.createEncryptor(cipher, iv.words);
			 */
			createEncryptor: function (cipher, iv) {
				return this.Encryptor.create(cipher, iv);
			},

			/**
			 * Creates this mode for decryption.
			 *
			 * @param {Cipher} cipher A block cipher instance.
			 * @param {Array} iv The IV words.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var mode = CryptoJS.mode.CBC.createDecryptor(cipher, iv.words);
			 */
			createDecryptor: function (cipher, iv) {
				return this.Decryptor.create(cipher, iv);
			},

			/**
			 * Initializes a newly created mode.
			 *
			 * @param {Cipher} cipher A block cipher instance.
			 * @param {Array} iv The IV words.
			 *
			 * @example
			 *
			 *     var mode = CryptoJS.mode.CBC.Encryptor.create(cipher, iv.words);
			 */
			init: function (cipher, iv) {
				this._cipher = cipher;
				this._iv = iv;
			}
		});

		/**
		 * Cipher Block Chaining mode.
		 */
		var CBC = C_mode.CBC = (function () {
			/**
			 * Abstract base CBC mode.
			 */
			var CBC = BlockCipherMode.extend();

			/**
			 * CBC encryptor.
			 */
			CBC.Encryptor = CBC.extend({
				/**
				 * Processes the data block at offset.
				 *
				 * @param {Array} words The data words to operate on.
				 * @param {number} offset The offset where the block starts.
				 *
				 * @example
				 *
				 *     mode.processBlock(data.words, offset);
				 */
				processBlock: function (words, offset) {
					// Shortcuts
					var cipher = this._cipher;
					var blockSize = cipher.blockSize;

					// XOR and encrypt
					xorBlock.call(this, words, offset, blockSize);
					cipher.encryptBlock(words, offset);

					// Remember this block to use with next block
					this._prevBlock = words.slice(offset, offset + blockSize);
				}
			});

			/**
			 * CBC decryptor.
			 */
			CBC.Decryptor = CBC.extend({
				/**
				 * Processes the data block at offset.
				 *
				 * @param {Array} words The data words to operate on.
				 * @param {number} offset The offset where the block starts.
				 *
				 * @example
				 *
				 *     mode.processBlock(data.words, offset);
				 */
				processBlock: function (words, offset) {
					// Shortcuts
					var cipher = this._cipher;
					var blockSize = cipher.blockSize;

					// Remember this block to use with next block
					var thisBlock = words.slice(offset, offset + blockSize);

					// Decrypt and XOR
					cipher.decryptBlock(words, offset);
					xorBlock.call(this, words, offset, blockSize);

					// This block becomes the previous block
					this._prevBlock = thisBlock;
				}
			});

			function xorBlock(words, offset, blockSize) {
				var block;

				// Shortcut
				var iv = this._iv;

				// Choose mixing block
				if (iv) {
					block = iv;

					// Remove IV for subsequent blocks
					this._iv = undefined;
				} else {
					block = this._prevBlock;
				}

				// XOR blocks
				for (var i = 0; i < blockSize; i++) {
					words[offset + i] ^= block[i];
				}
			}

			return CBC;
		}());

		/**
		 * Padding namespace.
		 */
		var C_pad = C.pad = {};

		/**
		 * PKCS #5/7 padding strategy.
		 */
		var Pkcs7 = C_pad.Pkcs7 = {
			/**
			 * Pads data using the algorithm defined in PKCS #5/7.
			 *
			 * @param {WordArray} data The data to pad.
			 * @param {number} blockSize The multiple that the data should be padded to.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     CryptoJS.pad.Pkcs7.pad(wordArray, 4);
			 */
			pad: function (data, blockSize) {
				// Shortcut
				var blockSizeBytes = blockSize * 4;

				// Count padding bytes
				var nPaddingBytes = blockSizeBytes - data.sigBytes % blockSizeBytes;

				// Create padding word
				var paddingWord = (nPaddingBytes << 24) | (nPaddingBytes << 16) | (nPaddingBytes << 8) | nPaddingBytes;

				// Create padding
				var paddingWords = [];
				for (var i = 0; i < nPaddingBytes; i += 4) {
					paddingWords.push(paddingWord);
				}
				var padding = WordArray.create(paddingWords, nPaddingBytes);

				// Add padding
				data.concat(padding);
			},

			/**
			 * Unpads data that had been padded using the algorithm defined in PKCS #5/7.
			 *
			 * @param {WordArray} data The data to unpad.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     CryptoJS.pad.Pkcs7.unpad(wordArray);
			 */
			unpad: function (data) {
				// Get number of padding bytes from last byte
				var nPaddingBytes = data.words[(data.sigBytes - 1) >>> 2] & 0xff;

				// Remove padding
				data.sigBytes -= nPaddingBytes;
			}
		};

		/**
		 * Abstract base block cipher template.
		 *
		 * @property {number} blockSize The number of 32-bit words this cipher operates on. Default: 4 (128 bits)
		 */
		var BlockCipher = C_lib.BlockCipher = Cipher.extend({
			/**
			 * Configuration options.
			 *
			 * @property {Mode} mode The block mode to use. Default: CBC
			 * @property {Padding} padding The padding strategy to use. Default: Pkcs7
			 */
			cfg: Cipher.cfg.extend({
				mode: CBC,
				padding: Pkcs7
			}),

			reset: function () {
				var modeCreator;

				// Reset cipher
				Cipher.reset.call(this);

				// Shortcuts
				var cfg = this.cfg;
				var iv = cfg.iv;
				var mode = cfg.mode;

				// Reset block mode
				if (this._xformMode == this._ENC_XFORM_MODE) {
					modeCreator = mode.createEncryptor;
				} else /* if (this._xformMode == this._DEC_XFORM_MODE) */ {
					modeCreator = mode.createDecryptor;
					// Keep at least one block in the buffer for unpadding
					this._minBufferSize = 1;
				}

				if (this._mode && this._mode.__creator == modeCreator) {
					this._mode.init(this, iv && iv.words);
				} else {
					this._mode = modeCreator.call(mode, this, iv && iv.words);
					this._mode.__creator = modeCreator;
				}
			},

			_doProcessBlock: function (words, offset) {
				this._mode.processBlock(words, offset);
			},

			_doFinalize: function () {
				var finalProcessedBlocks;

				// Shortcut
				var padding = this.cfg.padding;

				// Finalize
				if (this._xformMode == this._ENC_XFORM_MODE) {
					// Pad data
					padding.pad(this._data, this.blockSize);

					// Process final blocks
					finalProcessedBlocks = this._process(!!'flush');
				} else /* if (this._xformMode == this._DEC_XFORM_MODE) */ {
					// Process final blocks
					finalProcessedBlocks = this._process(!!'flush');

					// Unpad data
					padding.unpad(finalProcessedBlocks);
				}

				return finalProcessedBlocks;
			},

			blockSize: 128 / 32
		});

		/**
		 * A collection of cipher parameters.
		 *
		 * @property {WordArray} ciphertext The raw ciphertext.
		 * @property {WordArray} key The key to this ciphertext.
		 * @property {WordArray} iv The IV used in the ciphering operation.
		 * @property {WordArray} salt The salt used with a key derivation function.
		 * @property {Cipher} algorithm The cipher algorithm.
		 * @property {Mode} mode The block mode used in the ciphering operation.
		 * @property {Padding} padding The padding scheme used in the ciphering operation.
		 * @property {number} blockSize The block size of the cipher.
		 * @property {Format} formatter The default formatting strategy to convert this cipher params object to a string.
		 */
		var CipherParams = C_lib.CipherParams = Base.extend({
			/**
			 * Initializes a newly created cipher params object.
			 *
			 * @param {Object} cipherParams An object with any of the possible cipher parameters.
			 *
			 * @example
			 *
			 *     var cipherParams = CryptoJS.lib.CipherParams.create({
			 *         ciphertext: ciphertextWordArray,
			 *         key: keyWordArray,
			 *         iv: ivWordArray,
			 *         salt: saltWordArray,
			 *         algorithm: CryptoJS.algo.AES,
			 *         mode: CryptoJS.mode.CBC,
			 *         padding: CryptoJS.pad.PKCS7,
			 *         blockSize: 4,
			 *         formatter: CryptoJS.format.OpenSSL
			 *     });
			 */
			init: function (cipherParams) {
				this.mixIn(cipherParams);
			},

			/**
			 * Converts this cipher params object to a string.
			 *
			 * @param {Format} formatter (Optional) The formatting strategy to use.
			 *
			 * @return {string} The stringified cipher params.
			 *
			 * @throws Error If neither the formatter nor the default formatter is set.
			 *
			 * @example
			 *
			 *     var string = cipherParams + '';
			 *     var string = cipherParams.toString();
			 *     var string = cipherParams.toString(CryptoJS.format.OpenSSL);
			 */
			toString: function (formatter) {
				return (formatter || this.formatter).stringify(this);
			}
		});

		/**
		 * Format namespace.
		 */
		var C_format = C.format = {};

		/**
		 * OpenSSL formatting strategy.
		 */
		var OpenSSLFormatter = C_format.OpenSSL = {
			/**
			 * Converts a cipher params object to an OpenSSL-compatible string.
			 *
			 * @param {CipherParams} cipherParams The cipher params object.
			 *
			 * @return {string} The OpenSSL-compatible string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var openSSLString = CryptoJS.format.OpenSSL.stringify(cipherParams);
			 */
			stringify: function (cipherParams) {
				var wordArray;

				// Shortcuts
				var ciphertext = cipherParams.ciphertext;
				var salt = cipherParams.salt;

				// Format
				if (salt) {
					wordArray = WordArray.create([0x53616c74, 0x65645f5f]).concat(salt).concat(ciphertext);
				} else {
					wordArray = ciphertext;
				}

				return wordArray.toString(Base64);
			},

			/**
			 * Converts an OpenSSL-compatible string to a cipher params object.
			 *
			 * @param {string} openSSLStr The OpenSSL-compatible string.
			 *
			 * @return {CipherParams} The cipher params object.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var cipherParams = CryptoJS.format.OpenSSL.parse(openSSLString);
			 */
			parse: function (openSSLStr) {
				var salt;

				// Parse base64
				var ciphertext = Base64.parse(openSSLStr);

				// Shortcut
				var ciphertextWords = ciphertext.words;

				// Test for salt
				if (ciphertextWords[0] == 0x53616c74 && ciphertextWords[1] == 0x65645f5f) {
					// Extract salt
					salt = WordArray.create(ciphertextWords.slice(2, 4));

					// Remove salt from ciphertext
					ciphertextWords.splice(0, 4);
					ciphertext.sigBytes -= 16;
				}

				return CipherParams.create({ ciphertext: ciphertext, salt: salt });
			}
		};

		/**
		 * A cipher wrapper that returns ciphertext as a serializable cipher params object.
		 */
		var SerializableCipher = C_lib.SerializableCipher = Base.extend({
			/**
			 * Configuration options.
			 *
			 * @property {Formatter} format The formatting strategy to convert cipher param objects to and from a string. Default: OpenSSL
			 */
			cfg: Base.extend({
				format: OpenSSLFormatter
			}),

			/**
			 * Encrypts a message.
			 *
			 * @param {Cipher} cipher The cipher algorithm to use.
			 * @param {WordArray|string} message The message to encrypt.
			 * @param {WordArray} key The key.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @return {CipherParams} A cipher params object.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var ciphertextParams = CryptoJS.lib.SerializableCipher.encrypt(CryptoJS.algo.AES, message, key);
			 *     var ciphertextParams = CryptoJS.lib.SerializableCipher.encrypt(CryptoJS.algo.AES, message, key, { iv: iv });
			 *     var ciphertextParams = CryptoJS.lib.SerializableCipher.encrypt(CryptoJS.algo.AES, message, key, { iv: iv, format: CryptoJS.format.OpenSSL });
			 */
			encrypt: function (cipher, message, key, cfg) {
				// Apply config defaults
				cfg = this.cfg.extend(cfg);

				// Encrypt
				var encryptor = cipher.createEncryptor(key, cfg);
				var ciphertext = encryptor.finalize(message);

				// Shortcut
				var cipherCfg = encryptor.cfg;

				// Create and return serializable cipher params
				return CipherParams.create({
					ciphertext: ciphertext,
					key: key,
					iv: cipherCfg.iv,
					algorithm: cipher,
					mode: cipherCfg.mode,
					padding: cipherCfg.padding,
					blockSize: cipher.blockSize,
					formatter: cfg.format
				});
			},

			/**
			 * Decrypts serialized ciphertext.
			 *
			 * @param {Cipher} cipher The cipher algorithm to use.
			 * @param {CipherParams|string} ciphertext The ciphertext to decrypt.
			 * @param {WordArray} key The key.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @return {WordArray} The plaintext.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var plaintext = CryptoJS.lib.SerializableCipher.decrypt(CryptoJS.algo.AES, formattedCiphertext, key, { iv: iv, format: CryptoJS.format.OpenSSL });
			 *     var plaintext = CryptoJS.lib.SerializableCipher.decrypt(CryptoJS.algo.AES, ciphertextParams, key, { iv: iv, format: CryptoJS.format.OpenSSL });
			 */
			decrypt: function (cipher, ciphertext, key, cfg) {
				// Apply config defaults
				cfg = this.cfg.extend(cfg);

				// Convert string to CipherParams
				ciphertext = this._parse(ciphertext, cfg.format);

				// Decrypt
				var plaintext = cipher.createDecryptor(key, cfg).finalize(ciphertext.ciphertext);

				return plaintext;
			},

			/**
			 * Converts serialized ciphertext to CipherParams,
			 * else assumed CipherParams already and returns ciphertext unchanged.
			 *
			 * @param {CipherParams|string} ciphertext The ciphertext.
			 * @param {Formatter} format The formatting strategy to use to parse serialized ciphertext.
			 *
			 * @return {CipherParams} The unserialized ciphertext.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var ciphertextParams = CryptoJS.lib.SerializableCipher._parse(ciphertextStringOrParams, format);
			 */
			_parse: function (ciphertext, format) {
				if (typeof ciphertext == 'string') {
					return format.parse(ciphertext, this);
				} else {
					return ciphertext;
				}
			}
		});

		/**
		 * Key derivation function namespace.
		 */
		var C_kdf = C.kdf = {};

		/**
		 * OpenSSL key derivation function.
		 */
		var OpenSSLKdf = C_kdf.OpenSSL = {
			/**
			 * Derives a key and IV from a password.
			 *
			 * @param {string} password The password to derive from.
			 * @param {number} keySize The size in words of the key to generate.
			 * @param {number} ivSize The size in words of the IV to generate.
			 * @param {WordArray|string} salt (Optional) A 64-bit salt to use. If omitted, a salt will be generated randomly.
			 *
			 * @return {CipherParams} A cipher params object with the key, IV, and salt.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var derivedParams = CryptoJS.kdf.OpenSSL.execute('Password', 256/32, 128/32);
			 *     var derivedParams = CryptoJS.kdf.OpenSSL.execute('Password', 256/32, 128/32, 'saltsalt');
			 */
			execute: function (password, keySize, ivSize, salt) {
				// Generate random salt
				if (!salt) {
					salt = WordArray.random(64 / 8);
				}

				// Derive key and IV
				var key = EvpKDF.create({ keySize: keySize + ivSize }).compute(password, salt);

				// Separate key and IV
				var iv = WordArray.create(key.words.slice(keySize), ivSize * 4);
				key.sigBytes = keySize * 4;

				// Return params
				return CipherParams.create({ key: key, iv: iv, salt: salt });
			}
		};

		/**
		 * A serializable cipher wrapper that derives the key from a password,
		 * and returns ciphertext as a serializable cipher params object.
		 */
		var PasswordBasedCipher = C_lib.PasswordBasedCipher = SerializableCipher.extend({
			/**
			 * Configuration options.
			 *
			 * @property {KDF} kdf The key derivation function to use to generate a key and IV from a password. Default: OpenSSL
			 */
			cfg: SerializableCipher.cfg.extend({
				kdf: OpenSSLKdf
			}),

			/**
			 * Encrypts a message using a password.
			 *
			 * @param {Cipher} cipher The cipher algorithm to use.
			 * @param {WordArray|string} message The message to encrypt.
			 * @param {string} password The password.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @return {CipherParams} A cipher params object.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var ciphertextParams = CryptoJS.lib.PasswordBasedCipher.encrypt(CryptoJS.algo.AES, message, 'password');
			 *     var ciphertextParams = CryptoJS.lib.PasswordBasedCipher.encrypt(CryptoJS.algo.AES, message, 'password', { format: CryptoJS.format.OpenSSL });
			 */
			encrypt: function (cipher, message, password, cfg) {
				// Apply config defaults
				cfg = this.cfg.extend(cfg);

				// Derive key and other params
				var derivedParams = cfg.kdf.execute(password, cipher.keySize, cipher.ivSize);

				// Add IV to config
				cfg.iv = derivedParams.iv;

				// Encrypt
				var ciphertext = SerializableCipher.encrypt.call(this, cipher, message, derivedParams.key, cfg);

				// Mix in derived params
				ciphertext.mixIn(derivedParams);

				return ciphertext;
			},

			/**
			 * Decrypts serialized ciphertext using a password.
			 *
			 * @param {Cipher} cipher The cipher algorithm to use.
			 * @param {CipherParams|string} ciphertext The ciphertext to decrypt.
			 * @param {string} password The password.
			 * @param {Object} cfg (Optional) The configuration options to use for this operation.
			 *
			 * @return {WordArray} The plaintext.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var plaintext = CryptoJS.lib.PasswordBasedCipher.decrypt(CryptoJS.algo.AES, formattedCiphertext, 'password', { format: CryptoJS.format.OpenSSL });
			 *     var plaintext = CryptoJS.lib.PasswordBasedCipher.decrypt(CryptoJS.algo.AES, ciphertextParams, 'password', { format: CryptoJS.format.OpenSSL });
			 */
			decrypt: function (cipher, ciphertext, password, cfg) {
				// Apply config defaults
				cfg = this.cfg.extend(cfg);

				// Convert string to CipherParams
				ciphertext = this._parse(ciphertext, cfg.format);

				// Derive key and other params
				var derivedParams = cfg.kdf.execute(password, cipher.keySize, cipher.ivSize, ciphertext.salt);

				// Add IV to config
				cfg.iv = derivedParams.iv;

				// Decrypt
				var plaintext = SerializableCipher.decrypt.call(this, cipher, ciphertext, derivedParams.key, cfg);

				return plaintext;
			}
		});
	}());


	/**
	 * Cipher Feedback block mode.
	 */
	CryptoJS.mode.CFB = (function () {
		var CFB = CryptoJS.lib.BlockCipherMode.extend();

		CFB.Encryptor = CFB.extend({
			processBlock: function (words, offset) {
				// Shortcuts
				var cipher = this._cipher;
				var blockSize = cipher.blockSize;

				generateKeystreamAndEncrypt.call(this, words, offset, blockSize, cipher);

				// Remember this block to use with next block
				this._prevBlock = words.slice(offset, offset + blockSize);
			}
		});

		CFB.Decryptor = CFB.extend({
			processBlock: function (words, offset) {
				// Shortcuts
				var cipher = this._cipher;
				var blockSize = cipher.blockSize;

				// Remember this block to use with next block
				var thisBlock = words.slice(offset, offset + blockSize);

				generateKeystreamAndEncrypt.call(this, words, offset, blockSize, cipher);

				// This block becomes the previous block
				this._prevBlock = thisBlock;
			}
		});

		function generateKeystreamAndEncrypt(words, offset, blockSize, cipher) {
			var keystream;

			// Shortcut
			var iv = this._iv;

			// Generate keystream
			if (iv) {
				keystream = iv.slice(0);

				// Remove IV for subsequent blocks
				this._iv = undefined;
			} else {
				keystream = this._prevBlock;
			}
			cipher.encryptBlock(keystream, 0);

			// Encrypt
			for (var i = 0; i < blockSize; i++) {
				words[offset + i] ^= keystream[i];
			}
		}

		return CFB;
	}());


	/**
	 * Electronic Codebook block mode.
	 */
	CryptoJS.mode.ECB = (function () {
		var ECB = CryptoJS.lib.BlockCipherMode.extend();

		ECB.Encryptor = ECB.extend({
			processBlock: function (words, offset) {
				this._cipher.encryptBlock(words, offset);
			}
		});

		ECB.Decryptor = ECB.extend({
			processBlock: function (words, offset) {
				this._cipher.decryptBlock(words, offset);
			}
		});

		return ECB;
	}());


	/**
	 * ANSI X.923 padding strategy.
	 */
	CryptoJS.pad.AnsiX923 = {
		pad: function (data, blockSize) {
			// Shortcuts
			var dataSigBytes = data.sigBytes;
			var blockSizeBytes = blockSize * 4;

			// Count padding bytes
			var nPaddingBytes = blockSizeBytes - dataSigBytes % blockSizeBytes;

			// Compute last byte position
			var lastBytePos = dataSigBytes + nPaddingBytes - 1;

			// Pad
			data.clamp();
			data.words[lastBytePos >>> 2] |= nPaddingBytes << (24 - (lastBytePos % 4) * 8);
			data.sigBytes += nPaddingBytes;
		},

		unpad: function (data) {
			// Get number of padding bytes from last byte
			var nPaddingBytes = data.words[(data.sigBytes - 1) >>> 2] & 0xff;

			// Remove padding
			data.sigBytes -= nPaddingBytes;
		}
	};


	/**
	 * ISO 10126 padding strategy.
	 */
	CryptoJS.pad.Iso10126 = {
		pad: function (data, blockSize) {
			// Shortcut
			var blockSizeBytes = blockSize * 4;

			// Count padding bytes
			var nPaddingBytes = blockSizeBytes - data.sigBytes % blockSizeBytes;

			// Pad
			data.concat(CryptoJS.lib.WordArray.random(nPaddingBytes - 1)).
				concat(CryptoJS.lib.WordArray.create([nPaddingBytes << 24], 1));
		},

		unpad: function (data) {
			// Get number of padding bytes from last byte
			var nPaddingBytes = data.words[(data.sigBytes - 1) >>> 2] & 0xff;

			// Remove padding
			data.sigBytes -= nPaddingBytes;
		}
	};


	/**
	 * ISO/IEC 9797-1 Padding Method 2.
	 */
	CryptoJS.pad.Iso97971 = {
		pad: function (data, blockSize) {
			// Add 0x80 byte
			data.concat(CryptoJS.lib.WordArray.create([0x80000000], 1));

			// Zero pad the rest
			CryptoJS.pad.ZeroPadding.pad(data, blockSize);
		},

		unpad: function (data) {
			// Remove zero padding
			CryptoJS.pad.ZeroPadding.unpad(data);

			// Remove one more byte -- the 0x80 byte
			data.sigBytes--;
		}
	};


	/**
	 * Output Feedback block mode.
	 */
	CryptoJS.mode.OFB = (function () {
		var OFB = CryptoJS.lib.BlockCipherMode.extend();

		var Encryptor = OFB.Encryptor = OFB.extend({
			processBlock: function (words, offset) {
				// Shortcuts
				var cipher = this._cipher
				var blockSize = cipher.blockSize;
				var iv = this._iv;
				var keystream = this._keystream;

				// Generate keystream
				if (iv) {
					keystream = this._keystream = iv.slice(0);

					// Remove IV for subsequent blocks
					this._iv = undefined;
				}
				cipher.encryptBlock(keystream, 0);

				// Encrypt
				for (var i = 0; i < blockSize; i++) {
					words[offset + i] ^= keystream[i];
				}
			}
		});

		OFB.Decryptor = Encryptor;

		return OFB;
	}());


	/**
	 * A noop padding strategy.
	 */
	CryptoJS.pad.NoPadding = {
		pad: function () {
		},

		unpad: function () {
		}
	};


	(function (undefined) {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var CipherParams = C_lib.CipherParams;
		var C_enc = C.enc;
		var Hex = C_enc.Hex;
		var C_format = C.format;

		var HexFormatter = C_format.Hex = {
			/**
			 * Converts the ciphertext of a cipher params object to a hexadecimally encoded string.
			 *
			 * @param {CipherParams} cipherParams The cipher params object.
			 *
			 * @return {string} The hexadecimally encoded string.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var hexString = CryptoJS.format.Hex.stringify(cipherParams);
			 */
			stringify: function (cipherParams) {
				return cipherParams.ciphertext.toString(Hex);
			},

			/**
			 * Converts a hexadecimally encoded ciphertext string to a cipher params object.
			 *
			 * @param {string} input The hexadecimally encoded string.
			 *
			 * @return {CipherParams} The cipher params object.
			 *
			 * @static
			 *
			 * @example
			 *
			 *     var cipherParams = CryptoJS.format.Hex.parse(hexString);
			 */
			parse: function (input) {
				var ciphertext = Hex.parse(input);
				return CipherParams.create({ ciphertext: ciphertext });
			}
		};
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var BlockCipher = C_lib.BlockCipher;
		var C_algo = C.algo;

		// Lookup tables
		var SBOX = [];
		var INV_SBOX = [];
		var SUB_MIX_0 = [];
		var SUB_MIX_1 = [];
		var SUB_MIX_2 = [];
		var SUB_MIX_3 = [];
		var INV_SUB_MIX_0 = [];
		var INV_SUB_MIX_1 = [];
		var INV_SUB_MIX_2 = [];
		var INV_SUB_MIX_3 = [];

		// Compute lookup tables
		(function () {
			// Compute double table
			var d = [];
			for (var i = 0; i < 256; i++) {
				if (i < 128) {
					d[i] = i << 1;
				} else {
					d[i] = (i << 1) ^ 0x11b;
				}
			}

			// Walk GF(2^8)
			var x = 0;
			var xi = 0;
			for (var i = 0; i < 256; i++) {
				// Compute sbox
				var sx = xi ^ (xi << 1) ^ (xi << 2) ^ (xi << 3) ^ (xi << 4);
				sx = (sx >>> 8) ^ (sx & 0xff) ^ 0x63;
				SBOX[x] = sx;
				INV_SBOX[sx] = x;

				// Compute multiplication
				var x2 = d[x];
				var x4 = d[x2];
				var x8 = d[x4];

				// Compute sub bytes, mix columns tables
				var t = (d[sx] * 0x101) ^ (sx * 0x1010100);
				SUB_MIX_0[x] = (t << 24) | (t >>> 8);
				SUB_MIX_1[x] = (t << 16) | (t >>> 16);
				SUB_MIX_2[x] = (t << 8) | (t >>> 24);
				SUB_MIX_3[x] = t;

				// Compute inv sub bytes, inv mix columns tables
				var t = (x8 * 0x1010101) ^ (x4 * 0x10001) ^ (x2 * 0x101) ^ (x * 0x1010100);
				INV_SUB_MIX_0[sx] = (t << 24) | (t >>> 8);
				INV_SUB_MIX_1[sx] = (t << 16) | (t >>> 16);
				INV_SUB_MIX_2[sx] = (t << 8) | (t >>> 24);
				INV_SUB_MIX_3[sx] = t;

				// Compute next counter
				if (!x) {
					x = xi = 1;
				} else {
					x = x2 ^ d[d[d[x8 ^ x2]]];
					xi ^= d[d[xi]];
				}
			}
		}());

		// Precomputed Rcon lookup
		var RCON = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

		/**
		 * AES block cipher algorithm.
		 */
		var AES = C_algo.AES = BlockCipher.extend({
			_doReset: function () {
				var t;

				// Skip reset of nRounds has been set before and key did not change
				if (this._nRounds && this._keyPriorReset === this._key) {
					return;
				}

				// Shortcuts
				var key = this._keyPriorReset = this._key;
				var keyWords = key.words;
				var keySize = key.sigBytes / 4;

				// Compute number of rounds
				var nRounds = this._nRounds = keySize + 6;

				// Compute number of key schedule rows
				var ksRows = (nRounds + 1) * 4;

				// Compute key schedule
				var keySchedule = this._keySchedule = [];
				for (var ksRow = 0; ksRow < ksRows; ksRow++) {
					if (ksRow < keySize) {
						keySchedule[ksRow] = keyWords[ksRow];
					} else {
						t = keySchedule[ksRow - 1];

						if (!(ksRow % keySize)) {
							// Rot word
							t = (t << 8) | (t >>> 24);

							// Sub word
							t = (SBOX[t >>> 24] << 24) | (SBOX[(t >>> 16) & 0xff] << 16) | (SBOX[(t >>> 8) & 0xff] << 8) | SBOX[t & 0xff];

							// Mix Rcon
							t ^= RCON[(ksRow / keySize) | 0] << 24;
						} else if (keySize > 6 && ksRow % keySize == 4) {
							// Sub word
							t = (SBOX[t >>> 24] << 24) | (SBOX[(t >>> 16) & 0xff] << 16) | (SBOX[(t >>> 8) & 0xff] << 8) | SBOX[t & 0xff];
						}

						keySchedule[ksRow] = keySchedule[ksRow - keySize] ^ t;
					}
				}

				// Compute inv key schedule
				var invKeySchedule = this._invKeySchedule = [];
				for (var invKsRow = 0; invKsRow < ksRows; invKsRow++) {
					var ksRow = ksRows - invKsRow;

					if (invKsRow % 4) {
						var t = keySchedule[ksRow];
					} else {
						var t = keySchedule[ksRow - 4];
					}

					if (invKsRow < 4 || ksRow <= 4) {
						invKeySchedule[invKsRow] = t;
					} else {
						invKeySchedule[invKsRow] = INV_SUB_MIX_0[SBOX[t >>> 24]] ^ INV_SUB_MIX_1[SBOX[(t >>> 16) & 0xff]] ^
							INV_SUB_MIX_2[SBOX[(t >>> 8) & 0xff]] ^ INV_SUB_MIX_3[SBOX[t & 0xff]];
					}
				}
			},

			encryptBlock: function (M, offset) {
				this._doCryptBlock(M, offset, this._keySchedule, SUB_MIX_0, SUB_MIX_1, SUB_MIX_2, SUB_MIX_3, SBOX);
			},

			decryptBlock: function (M, offset) {
				// Swap 2nd and 4th rows
				var t = M[offset + 1];
				M[offset + 1] = M[offset + 3];
				M[offset + 3] = t;

				this._doCryptBlock(M, offset, this._invKeySchedule, INV_SUB_MIX_0, INV_SUB_MIX_1, INV_SUB_MIX_2, INV_SUB_MIX_3, INV_SBOX);

				// Inv swap 2nd and 4th rows
				var t = M[offset + 1];
				M[offset + 1] = M[offset + 3];
				M[offset + 3] = t;
			},

			_doCryptBlock: function (M, offset, keySchedule, SUB_MIX_0, SUB_MIX_1, SUB_MIX_2, SUB_MIX_3, SBOX) {
				// Shortcut
				var nRounds = this._nRounds;

				// Get input, add round key
				var s0 = M[offset] ^ keySchedule[0];
				var s1 = M[offset + 1] ^ keySchedule[1];
				var s2 = M[offset + 2] ^ keySchedule[2];
				var s3 = M[offset + 3] ^ keySchedule[3];

				// Key schedule row counter
				var ksRow = 4;

				// Rounds
				for (var round = 1; round < nRounds; round++) {
					// Shift rows, sub bytes, mix columns, add round key
					var t0 = SUB_MIX_0[s0 >>> 24] ^ SUB_MIX_1[(s1 >>> 16) & 0xff] ^ SUB_MIX_2[(s2 >>> 8) & 0xff] ^ SUB_MIX_3[s3 & 0xff] ^ keySchedule[ksRow++];
					var t1 = SUB_MIX_0[s1 >>> 24] ^ SUB_MIX_1[(s2 >>> 16) & 0xff] ^ SUB_MIX_2[(s3 >>> 8) & 0xff] ^ SUB_MIX_3[s0 & 0xff] ^ keySchedule[ksRow++];
					var t2 = SUB_MIX_0[s2 >>> 24] ^ SUB_MIX_1[(s3 >>> 16) & 0xff] ^ SUB_MIX_2[(s0 >>> 8) & 0xff] ^ SUB_MIX_3[s1 & 0xff] ^ keySchedule[ksRow++];
					var t3 = SUB_MIX_0[s3 >>> 24] ^ SUB_MIX_1[(s0 >>> 16) & 0xff] ^ SUB_MIX_2[(s1 >>> 8) & 0xff] ^ SUB_MIX_3[s2 & 0xff] ^ keySchedule[ksRow++];

					// Update state
					s0 = t0;
					s1 = t1;
					s2 = t2;
					s3 = t3;
				}

				// Shift rows, sub bytes, add round key
				var t0 = ((SBOX[s0 >>> 24] << 24) | (SBOX[(s1 >>> 16) & 0xff] << 16) | (SBOX[(s2 >>> 8) & 0xff] << 8) | SBOX[s3 & 0xff]) ^ keySchedule[ksRow++];
				var t1 = ((SBOX[s1 >>> 24] << 24) | (SBOX[(s2 >>> 16) & 0xff] << 16) | (SBOX[(s3 >>> 8) & 0xff] << 8) | SBOX[s0 & 0xff]) ^ keySchedule[ksRow++];
				var t2 = ((SBOX[s2 >>> 24] << 24) | (SBOX[(s3 >>> 16) & 0xff] << 16) | (SBOX[(s0 >>> 8) & 0xff] << 8) | SBOX[s1 & 0xff]) ^ keySchedule[ksRow++];
				var t3 = ((SBOX[s3 >>> 24] << 24) | (SBOX[(s0 >>> 16) & 0xff] << 16) | (SBOX[(s1 >>> 8) & 0xff] << 8) | SBOX[s2 & 0xff]) ^ keySchedule[ksRow++];

				// Set output
				M[offset] = t0;
				M[offset + 1] = t1;
				M[offset + 2] = t2;
				M[offset + 3] = t3;
			},

			keySize: 256 / 32
		});

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.AES.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.AES.decrypt(ciphertext, key, cfg);
		 */
		C.AES = BlockCipher._createHelper(AES);
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var WordArray = C_lib.WordArray;
		var BlockCipher = C_lib.BlockCipher;
		var C_algo = C.algo;

		// Permuted Choice 1 constants
		var PC1 = [
			57, 49, 41, 33, 25, 17, 9, 1,
			58, 50, 42, 34, 26, 18, 10, 2,
			59, 51, 43, 35, 27, 19, 11, 3,
			60, 52, 44, 36, 63, 55, 47, 39,
			31, 23, 15, 7, 62, 54, 46, 38,
			30, 22, 14, 6, 61, 53, 45, 37,
			29, 21, 13, 5, 28, 20, 12, 4
		];

		// Permuted Choice 2 constants
		var PC2 = [
			14, 17, 11, 24, 1, 5,
			3, 28, 15, 6, 21, 10,
			23, 19, 12, 4, 26, 8,
			16, 7, 27, 20, 13, 2,
			41, 52, 31, 37, 47, 55,
			30, 40, 51, 45, 33, 48,
			44, 49, 39, 56, 34, 53,
			46, 42, 50, 36, 29, 32
		];

		// Cumulative bit shift constants
		var BIT_SHIFTS = [1, 2, 4, 6, 8, 10, 12, 14, 15, 17, 19, 21, 23, 25, 27, 28];

		// SBOXes and round permutation constants
		var SBOX_P = [
			{
				0x0: 0x808200,
				0x10000000: 0x8000,
				0x20000000: 0x808002,
				0x30000000: 0x2,
				0x40000000: 0x200,
				0x50000000: 0x808202,
				0x60000000: 0x800202,
				0x70000000: 0x800000,
				0x80000000: 0x202,
				0x90000000: 0x800200,
				0xa0000000: 0x8200,
				0xb0000000: 0x808000,
				0xc0000000: 0x8002,
				0xd0000000: 0x800002,
				0xe0000000: 0x0,
				0xf0000000: 0x8202,
				0x8000000: 0x0,
				0x18000000: 0x808202,
				0x28000000: 0x8202,
				0x38000000: 0x8000,
				0x48000000: 0x808200,
				0x58000000: 0x200,
				0x68000000: 0x808002,
				0x78000000: 0x2,
				0x88000000: 0x800200,
				0x98000000: 0x8200,
				0xa8000000: 0x808000,
				0xb8000000: 0x800202,
				0xc8000000: 0x800002,
				0xd8000000: 0x8002,
				0xe8000000: 0x202,
				0xf8000000: 0x800000,
				0x1: 0x8000,
				0x10000001: 0x2,
				0x20000001: 0x808200,
				0x30000001: 0x800000,
				0x40000001: 0x808002,
				0x50000001: 0x8200,
				0x60000001: 0x200,
				0x70000001: 0x800202,
				0x80000001: 0x808202,
				0x90000001: 0x808000,
				0xa0000001: 0x800002,
				0xb0000001: 0x8202,
				0xc0000001: 0x202,
				0xd0000001: 0x800200,
				0xe0000001: 0x8002,
				0xf0000001: 0x0,
				0x8000001: 0x808202,
				0x18000001: 0x808000,
				0x28000001: 0x800000,
				0x38000001: 0x200,
				0x48000001: 0x8000,
				0x58000001: 0x800002,
				0x68000001: 0x2,
				0x78000001: 0x8202,
				0x88000001: 0x8002,
				0x98000001: 0x800202,
				0xa8000001: 0x202,
				0xb8000001: 0x808200,
				0xc8000001: 0x800200,
				0xd8000001: 0x0,
				0xe8000001: 0x8200,
				0xf8000001: 0x808002
			},
			{
				0x0: 0x40084010,
				0x1000000: 0x4000,
				0x2000000: 0x80000,
				0x3000000: 0x40080010,
				0x4000000: 0x40000010,
				0x5000000: 0x40084000,
				0x6000000: 0x40004000,
				0x7000000: 0x10,
				0x8000000: 0x84000,
				0x9000000: 0x40004010,
				0xa000000: 0x40000000,
				0xb000000: 0x84010,
				0xc000000: 0x80010,
				0xd000000: 0x0,
				0xe000000: 0x4010,
				0xf000000: 0x40080000,
				0x800000: 0x40004000,
				0x1800000: 0x84010,
				0x2800000: 0x10,
				0x3800000: 0x40004010,
				0x4800000: 0x40084010,
				0x5800000: 0x40000000,
				0x6800000: 0x80000,
				0x7800000: 0x40080010,
				0x8800000: 0x80010,
				0x9800000: 0x0,
				0xa800000: 0x4000,
				0xb800000: 0x40080000,
				0xc800000: 0x40000010,
				0xd800000: 0x84000,
				0xe800000: 0x40084000,
				0xf800000: 0x4010,
				0x10000000: 0x0,
				0x11000000: 0x40080010,
				0x12000000: 0x40004010,
				0x13000000: 0x40084000,
				0x14000000: 0x40080000,
				0x15000000: 0x10,
				0x16000000: 0x84010,
				0x17000000: 0x4000,
				0x18000000: 0x4010,
				0x19000000: 0x80000,
				0x1a000000: 0x80010,
				0x1b000000: 0x40000010,
				0x1c000000: 0x84000,
				0x1d000000: 0x40004000,
				0x1e000000: 0x40000000,
				0x1f000000: 0x40084010,
				0x10800000: 0x84010,
				0x11800000: 0x80000,
				0x12800000: 0x40080000,
				0x13800000: 0x4000,
				0x14800000: 0x40004000,
				0x15800000: 0x40084010,
				0x16800000: 0x10,
				0x17800000: 0x40000000,
				0x18800000: 0x40084000,
				0x19800000: 0x40000010,
				0x1a800000: 0x40004010,
				0x1b800000: 0x80010,
				0x1c800000: 0x0,
				0x1d800000: 0x4010,
				0x1e800000: 0x40080010,
				0x1f800000: 0x84000
			},
			{
				0x0: 0x104,
				0x100000: 0x0,
				0x200000: 0x4000100,
				0x300000: 0x10104,
				0x400000: 0x10004,
				0x500000: 0x4000004,
				0x600000: 0x4010104,
				0x700000: 0x4010000,
				0x800000: 0x4000000,
				0x900000: 0x4010100,
				0xa00000: 0x10100,
				0xb00000: 0x4010004,
				0xc00000: 0x4000104,
				0xd00000: 0x10000,
				0xe00000: 0x4,
				0xf00000: 0x100,
				0x80000: 0x4010100,
				0x180000: 0x4010004,
				0x280000: 0x0,
				0x380000: 0x4000100,
				0x480000: 0x4000004,
				0x580000: 0x10000,
				0x680000: 0x10004,
				0x780000: 0x104,
				0x880000: 0x4,
				0x980000: 0x100,
				0xa80000: 0x4010000,
				0xb80000: 0x10104,
				0xc80000: 0x10100,
				0xd80000: 0x4000104,
				0xe80000: 0x4010104,
				0xf80000: 0x4000000,
				0x1000000: 0x4010100,
				0x1100000: 0x10004,
				0x1200000: 0x10000,
				0x1300000: 0x4000100,
				0x1400000: 0x100,
				0x1500000: 0x4010104,
				0x1600000: 0x4000004,
				0x1700000: 0x0,
				0x1800000: 0x4000104,
				0x1900000: 0x4000000,
				0x1a00000: 0x4,
				0x1b00000: 0x10100,
				0x1c00000: 0x4010000,
				0x1d00000: 0x104,
				0x1e00000: 0x10104,
				0x1f00000: 0x4010004,
				0x1080000: 0x4000000,
				0x1180000: 0x104,
				0x1280000: 0x4010100,
				0x1380000: 0x0,
				0x1480000: 0x10004,
				0x1580000: 0x4000100,
				0x1680000: 0x100,
				0x1780000: 0x4010004,
				0x1880000: 0x10000,
				0x1980000: 0x4010104,
				0x1a80000: 0x10104,
				0x1b80000: 0x4000004,
				0x1c80000: 0x4000104,
				0x1d80000: 0x4010000,
				0x1e80000: 0x4,
				0x1f80000: 0x10100
			},
			{
				0x0: 0x80401000,
				0x10000: 0x80001040,
				0x20000: 0x401040,
				0x30000: 0x80400000,
				0x40000: 0x0,
				0x50000: 0x401000,
				0x60000: 0x80000040,
				0x70000: 0x400040,
				0x80000: 0x80000000,
				0x90000: 0x400000,
				0xa0000: 0x40,
				0xb0000: 0x80001000,
				0xc0000: 0x80400040,
				0xd0000: 0x1040,
				0xe0000: 0x1000,
				0xf0000: 0x80401040,
				0x8000: 0x80001040,
				0x18000: 0x40,
				0x28000: 0x80400040,
				0x38000: 0x80001000,
				0x48000: 0x401000,
				0x58000: 0x80401040,
				0x68000: 0x0,
				0x78000: 0x80400000,
				0x88000: 0x1000,
				0x98000: 0x80401000,
				0xa8000: 0x400000,
				0xb8000: 0x1040,
				0xc8000: 0x80000000,
				0xd8000: 0x400040,
				0xe8000: 0x401040,
				0xf8000: 0x80000040,
				0x100000: 0x400040,
				0x110000: 0x401000,
				0x120000: 0x80000040,
				0x130000: 0x0,
				0x140000: 0x1040,
				0x150000: 0x80400040,
				0x160000: 0x80401000,
				0x170000: 0x80001040,
				0x180000: 0x80401040,
				0x190000: 0x80000000,
				0x1a0000: 0x80400000,
				0x1b0000: 0x401040,
				0x1c0000: 0x80001000,
				0x1d0000: 0x400000,
				0x1e0000: 0x40,
				0x1f0000: 0x1000,
				0x108000: 0x80400000,
				0x118000: 0x80401040,
				0x128000: 0x0,
				0x138000: 0x401000,
				0x148000: 0x400040,
				0x158000: 0x80000000,
				0x168000: 0x80001040,
				0x178000: 0x40,
				0x188000: 0x80000040,
				0x198000: 0x1000,
				0x1a8000: 0x80001000,
				0x1b8000: 0x80400040,
				0x1c8000: 0x1040,
				0x1d8000: 0x80401000,
				0x1e8000: 0x400000,
				0x1f8000: 0x401040
			},
			{
				0x0: 0x80,
				0x1000: 0x1040000,
				0x2000: 0x40000,
				0x3000: 0x20000000,
				0x4000: 0x20040080,
				0x5000: 0x1000080,
				0x6000: 0x21000080,
				0x7000: 0x40080,
				0x8000: 0x1000000,
				0x9000: 0x20040000,
				0xa000: 0x20000080,
				0xb000: 0x21040080,
				0xc000: 0x21040000,
				0xd000: 0x0,
				0xe000: 0x1040080,
				0xf000: 0x21000000,
				0x800: 0x1040080,
				0x1800: 0x21000080,
				0x2800: 0x80,
				0x3800: 0x1040000,
				0x4800: 0x40000,
				0x5800: 0x20040080,
				0x6800: 0x21040000,
				0x7800: 0x20000000,
				0x8800: 0x20040000,
				0x9800: 0x0,
				0xa800: 0x21040080,
				0xb800: 0x1000080,
				0xc800: 0x20000080,
				0xd800: 0x21000000,
				0xe800: 0x1000000,
				0xf800: 0x40080,
				0x10000: 0x40000,
				0x11000: 0x80,
				0x12000: 0x20000000,
				0x13000: 0x21000080,
				0x14000: 0x1000080,
				0x15000: 0x21040000,
				0x16000: 0x20040080,
				0x17000: 0x1000000,
				0x18000: 0x21040080,
				0x19000: 0x21000000,
				0x1a000: 0x1040000,
				0x1b000: 0x20040000,
				0x1c000: 0x40080,
				0x1d000: 0x20000080,
				0x1e000: 0x0,
				0x1f000: 0x1040080,
				0x10800: 0x21000080,
				0x11800: 0x1000000,
				0x12800: 0x1040000,
				0x13800: 0x20040080,
				0x14800: 0x20000000,
				0x15800: 0x1040080,
				0x16800: 0x80,
				0x17800: 0x21040000,
				0x18800: 0x40080,
				0x19800: 0x21040080,
				0x1a800: 0x0,
				0x1b800: 0x21000000,
				0x1c800: 0x1000080,
				0x1d800: 0x40000,
				0x1e800: 0x20040000,
				0x1f800: 0x20000080
			},
			{
				0x0: 0x10000008,
				0x100: 0x2000,
				0x200: 0x10200000,
				0x300: 0x10202008,
				0x400: 0x10002000,
				0x500: 0x200000,
				0x600: 0x200008,
				0x700: 0x10000000,
				0x800: 0x0,
				0x900: 0x10002008,
				0xa00: 0x202000,
				0xb00: 0x8,
				0xc00: 0x10200008,
				0xd00: 0x202008,
				0xe00: 0x2008,
				0xf00: 0x10202000,
				0x80: 0x10200000,
				0x180: 0x10202008,
				0x280: 0x8,
				0x380: 0x200000,
				0x480: 0x202008,
				0x580: 0x10000008,
				0x680: 0x10002000,
				0x780: 0x2008,
				0x880: 0x200008,
				0x980: 0x2000,
				0xa80: 0x10002008,
				0xb80: 0x10200008,
				0xc80: 0x0,
				0xd80: 0x10202000,
				0xe80: 0x202000,
				0xf80: 0x10000000,
				0x1000: 0x10002000,
				0x1100: 0x10200008,
				0x1200: 0x10202008,
				0x1300: 0x2008,
				0x1400: 0x200000,
				0x1500: 0x10000000,
				0x1600: 0x10000008,
				0x1700: 0x202000,
				0x1800: 0x202008,
				0x1900: 0x0,
				0x1a00: 0x8,
				0x1b00: 0x10200000,
				0x1c00: 0x2000,
				0x1d00: 0x10002008,
				0x1e00: 0x10202000,
				0x1f00: 0x200008,
				0x1080: 0x8,
				0x1180: 0x202000,
				0x1280: 0x200000,
				0x1380: 0x10000008,
				0x1480: 0x10002000,
				0x1580: 0x2008,
				0x1680: 0x10202008,
				0x1780: 0x10200000,
				0x1880: 0x10202000,
				0x1980: 0x10200008,
				0x1a80: 0x2000,
				0x1b80: 0x202008,
				0x1c80: 0x200008,
				0x1d80: 0x0,
				0x1e80: 0x10000000,
				0x1f80: 0x10002008
			},
			{
				0x0: 0x100000,
				0x10: 0x2000401,
				0x20: 0x400,
				0x30: 0x100401,
				0x40: 0x2100401,
				0x50: 0x0,
				0x60: 0x1,
				0x70: 0x2100001,
				0x80: 0x2000400,
				0x90: 0x100001,
				0xa0: 0x2000001,
				0xb0: 0x2100400,
				0xc0: 0x2100000,
				0xd0: 0x401,
				0xe0: 0x100400,
				0xf0: 0x2000000,
				0x8: 0x2100001,
				0x18: 0x0,
				0x28: 0x2000401,
				0x38: 0x2100400,
				0x48: 0x100000,
				0x58: 0x2000001,
				0x68: 0x2000000,
				0x78: 0x401,
				0x88: 0x100401,
				0x98: 0x2000400,
				0xa8: 0x2100000,
				0xb8: 0x100001,
				0xc8: 0x400,
				0xd8: 0x2100401,
				0xe8: 0x1,
				0xf8: 0x100400,
				0x100: 0x2000000,
				0x110: 0x100000,
				0x120: 0x2000401,
				0x130: 0x2100001,
				0x140: 0x100001,
				0x150: 0x2000400,
				0x160: 0x2100400,
				0x170: 0x100401,
				0x180: 0x401,
				0x190: 0x2100401,
				0x1a0: 0x100400,
				0x1b0: 0x1,
				0x1c0: 0x0,
				0x1d0: 0x2100000,
				0x1e0: 0x2000001,
				0x1f0: 0x400,
				0x108: 0x100400,
				0x118: 0x2000401,
				0x128: 0x2100001,
				0x138: 0x1,
				0x148: 0x2000000,
				0x158: 0x100000,
				0x168: 0x401,
				0x178: 0x2100400,
				0x188: 0x2000001,
				0x198: 0x2100000,
				0x1a8: 0x0,
				0x1b8: 0x2100401,
				0x1c8: 0x100401,
				0x1d8: 0x400,
				0x1e8: 0x2000400,
				0x1f8: 0x100001
			},
			{
				0x0: 0x8000820,
				0x1: 0x20000,
				0x2: 0x8000000,
				0x3: 0x20,
				0x4: 0x20020,
				0x5: 0x8020820,
				0x6: 0x8020800,
				0x7: 0x800,
				0x8: 0x8020000,
				0x9: 0x8000800,
				0xa: 0x20800,
				0xb: 0x8020020,
				0xc: 0x820,
				0xd: 0x0,
				0xe: 0x8000020,
				0xf: 0x20820,
				0x80000000: 0x800,
				0x80000001: 0x8020820,
				0x80000002: 0x8000820,
				0x80000003: 0x8000000,
				0x80000004: 0x8020000,
				0x80000005: 0x20800,
				0x80000006: 0x20820,
				0x80000007: 0x20,
				0x80000008: 0x8000020,
				0x80000009: 0x820,
				0x8000000a: 0x20020,
				0x8000000b: 0x8020800,
				0x8000000c: 0x0,
				0x8000000d: 0x8020020,
				0x8000000e: 0x8000800,
				0x8000000f: 0x20000,
				0x10: 0x20820,
				0x11: 0x8020800,
				0x12: 0x20,
				0x13: 0x800,
				0x14: 0x8000800,
				0x15: 0x8000020,
				0x16: 0x8020020,
				0x17: 0x20000,
				0x18: 0x0,
				0x19: 0x20020,
				0x1a: 0x8020000,
				0x1b: 0x8000820,
				0x1c: 0x8020820,
				0x1d: 0x20800,
				0x1e: 0x820,
				0x1f: 0x8000000,
				0x80000010: 0x20000,
				0x80000011: 0x800,
				0x80000012: 0x8020020,
				0x80000013: 0x20820,
				0x80000014: 0x20,
				0x80000015: 0x8020000,
				0x80000016: 0x8000000,
				0x80000017: 0x8000820,
				0x80000018: 0x8020820,
				0x80000019: 0x8000020,
				0x8000001a: 0x8000800,
				0x8000001b: 0x0,
				0x8000001c: 0x20800,
				0x8000001d: 0x820,
				0x8000001e: 0x20020,
				0x8000001f: 0x8020800
			}
		];

		// Masks that select the SBOX input
		var SBOX_MASK = [
			0xf8000001, 0x1f800000, 0x01f80000, 0x001f8000,
			0x0001f800, 0x00001f80, 0x000001f8, 0x8000001f
		];

		/**
		 * DES block cipher algorithm.
		 */
		var DES = C_algo.DES = BlockCipher.extend({
			_doReset: function () {
				// Shortcuts
				var key = this._key;
				var keyWords = key.words;

				// Select 56 bits according to PC1
				var keyBits = [];
				for (var i = 0; i < 56; i++) {
					var keyBitPos = PC1[i] - 1;
					keyBits[i] = (keyWords[keyBitPos >>> 5] >>> (31 - keyBitPos % 32)) & 1;
				}

				// Assemble 16 subkeys
				var subKeys = this._subKeys = [];
				for (var nSubKey = 0; nSubKey < 16; nSubKey++) {
					// Create subkey
					var subKey = subKeys[nSubKey] = [];

					// Shortcut
					var bitShift = BIT_SHIFTS[nSubKey];

					// Select 48 bits according to PC2
					for (var i = 0; i < 24; i++) {
						// Select from the left 28 key bits
						subKey[(i / 6) | 0] |= keyBits[((PC2[i] - 1) + bitShift) % 28] << (31 - i % 6);

						// Select from the right 28 key bits
						subKey[4 + ((i / 6) | 0)] |= keyBits[28 + (((PC2[i + 24] - 1) + bitShift) % 28)] << (31 - i % 6);
					}

					// Since each subkey is applied to an expanded 32-bit input,
					// the subkey can be broken into 8 values scaled to 32-bits,
					// which allows the key to be used without expansion
					subKey[0] = (subKey[0] << 1) | (subKey[0] >>> 31);
					for (var i = 1; i < 7; i++) {
						subKey[i] = subKey[i] >>> ((i - 1) * 4 + 3);
					}
					subKey[7] = (subKey[7] << 5) | (subKey[7] >>> 27);
				}

				// Compute inverse subkeys
				var invSubKeys = this._invSubKeys = [];
				for (var i = 0; i < 16; i++) {
					invSubKeys[i] = subKeys[15 - i];
				}
			},

			encryptBlock: function (M, offset) {
				this._doCryptBlock(M, offset, this._subKeys);
			},

			decryptBlock: function (M, offset) {
				this._doCryptBlock(M, offset, this._invSubKeys);
			},

			_doCryptBlock: function (M, offset, subKeys) {
				// Get input
				this._lBlock = M[offset];
				this._rBlock = M[offset + 1];

				// Initial permutation
				exchangeLR.call(this, 4, 0x0f0f0f0f);
				exchangeLR.call(this, 16, 0x0000ffff);
				exchangeRL.call(this, 2, 0x33333333);
				exchangeRL.call(this, 8, 0x00ff00ff);
				exchangeLR.call(this, 1, 0x55555555);

				// Rounds
				for (var round = 0; round < 16; round++) {
					// Shortcuts
					var subKey = subKeys[round];
					var lBlock = this._lBlock;
					var rBlock = this._rBlock;

					// Feistel function
					var f = 0;
					for (var i = 0; i < 8; i++) {
						f |= SBOX_P[i][((rBlock ^ subKey[i]) & SBOX_MASK[i]) >>> 0];
					}
					this._lBlock = rBlock;
					this._rBlock = lBlock ^ f;
				}

				// Undo swap from last round
				var t = this._lBlock;
				this._lBlock = this._rBlock;
				this._rBlock = t;

				// Final permutation
				exchangeLR.call(this, 1, 0x55555555);
				exchangeRL.call(this, 8, 0x00ff00ff);
				exchangeRL.call(this, 2, 0x33333333);
				exchangeLR.call(this, 16, 0x0000ffff);
				exchangeLR.call(this, 4, 0x0f0f0f0f);

				// Set output
				M[offset] = this._lBlock;
				M[offset + 1] = this._rBlock;
			},

			keySize: 64 / 32,

			ivSize: 64 / 32,

			blockSize: 64 / 32
		});

		// Swap bits across the left and right words
		function exchangeLR(offset, mask) {
			var t = ((this._lBlock >>> offset) ^ this._rBlock) & mask;
			this._rBlock ^= t;
			this._lBlock ^= t << offset;
		}

		function exchangeRL(offset, mask) {
			var t = ((this._rBlock >>> offset) ^ this._lBlock) & mask;
			this._lBlock ^= t;
			this._rBlock ^= t << offset;
		}

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.DES.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.DES.decrypt(ciphertext, key, cfg);
		 */
		C.DES = BlockCipher._createHelper(DES);

		/**
		 * Triple-DES block cipher algorithm.
		 */
		var TripleDES = C_algo.TripleDES = BlockCipher.extend({
			_doReset: function () {
				// Shortcuts
				var key = this._key;
				var keyWords = key.words;
				// Make sure the key length is valid (64, 128 or >= 192 bit)
				if (keyWords.length !== 2 && keyWords.length !== 4 && keyWords.length < 6) {
					throw new Error('Invalid key length - 3DES requires the key length to be 64, 128, 192 or >192.');
				}

				// Extend the key according to the keying options defined in 3DES standard
				var key1 = keyWords.slice(0, 2);
				var key2 = keyWords.length < 4 ? keyWords.slice(0, 2) : keyWords.slice(2, 4);
				var key3 = keyWords.length < 6 ? keyWords.slice(0, 2) : keyWords.slice(4, 6);

				// Create DES instances
				this._des1 = DES.createEncryptor(WordArray.create(key1));
				this._des2 = DES.createEncryptor(WordArray.create(key2));
				this._des3 = DES.createEncryptor(WordArray.create(key3));
			},

			encryptBlock: function (M, offset) {
				this._des1.encryptBlock(M, offset);
				this._des2.decryptBlock(M, offset);
				this._des3.encryptBlock(M, offset);
			},

			decryptBlock: function (M, offset) {
				this._des3.decryptBlock(M, offset);
				this._des2.encryptBlock(M, offset);
				this._des1.decryptBlock(M, offset);
			},

			keySize: 192 / 32,

			ivSize: 64 / 32,

			blockSize: 64 / 32
		});

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.TripleDES.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.TripleDES.decrypt(ciphertext, key, cfg);
		 */
		C.TripleDES = BlockCipher._createHelper(TripleDES);
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var StreamCipher = C_lib.StreamCipher;
		var C_algo = C.algo;

		/**
		 * RC4 stream cipher algorithm.
		 */
		var RC4 = C_algo.RC4 = StreamCipher.extend({
			_doReset: function () {
				// Shortcuts
				var key = this._key;
				var keyWords = key.words;
				var keySigBytes = key.sigBytes;

				// Init sbox
				var S = this._S = [];
				for (var i = 0; i < 256; i++) {
					S[i] = i;
				}

				// Key setup
				for (var i = 0, j = 0; i < 256; i++) {
					var keyByteIndex = i % keySigBytes;
					var keyByte = (keyWords[keyByteIndex >>> 2] >>> (24 - (keyByteIndex % 4) * 8)) & 0xff;

					j = (j + S[i] + keyByte) % 256;

					// Swap
					var t = S[i];
					S[i] = S[j];
					S[j] = t;
				}

				// Counters
				this._i = this._j = 0;
			},

			_doProcessBlock: function (M, offset) {
				M[offset] ^= generateKeystreamWord.call(this);
			},

			keySize: 256 / 32,

			ivSize: 0
		});

		function generateKeystreamWord() {
			// Shortcuts
			var S = this._S;
			var i = this._i;
			var j = this._j;

			// Generate keystream word
			var keystreamWord = 0;
			for (var n = 0; n < 4; n++) {
				i = (i + 1) % 256;
				j = (j + S[i]) % 256;

				// Swap
				var t = S[i];
				S[i] = S[j];
				S[j] = t;

				keystreamWord |= S[(S[i] + S[j]) % 256] << (24 - n * 8);
			}

			// Update counters
			this._i = i;
			this._j = j;

			return keystreamWord;
		}

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.RC4.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.RC4.decrypt(ciphertext, key, cfg);
		 */
		C.RC4 = StreamCipher._createHelper(RC4);

		/**
		 * Modified RC4 stream cipher algorithm.
		 */
		var RC4Drop = C_algo.RC4Drop = RC4.extend({
			/**
			 * Configuration options.
			 *
			 * @property {number} drop The number of keystream words to drop. Default 192
			 */
			cfg: RC4.cfg.extend({
				drop: 192
			}),

			_doReset: function () {
				RC4._doReset.call(this);

				// Drop
				for (var i = this.cfg.drop; i > 0; i--) {
					generateKeystreamWord.call(this);
				}
			}
		});

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.RC4Drop.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.RC4Drop.decrypt(ciphertext, key, cfg);
		 */
		C.RC4Drop = StreamCipher._createHelper(RC4Drop);
	}());


	/** @preserve
	 * Counter block mode compatible with  Dr Brian Gladman fileenc.c
	 * derived from CryptoJS.mode.CTR
	 * Jan Hruby jhruby.web@gmail.com
	 */
	CryptoJS.mode.CTRGladman = (function () {
		var CTRGladman = CryptoJS.lib.BlockCipherMode.extend();

		function incWord(word) {
			if (((word >> 24) & 0xff) === 0xff) { //overflow
				var b1 = (word >> 16) & 0xff;
				var b2 = (word >> 8) & 0xff;
				var b3 = word & 0xff;

				if (b1 === 0xff) // overflow b1
				{
					b1 = 0;
					if (b2 === 0xff) {
						b2 = 0;
						if (b3 === 0xff) {
							b3 = 0;
						}
						else {
							++b3;
						}
					}
					else {
						++b2;
					}
				}
				else {
					++b1;
				}

				word = 0;
				word += (b1 << 16);
				word += (b2 << 8);
				word += b3;
			}
			else {
				word += (0x01 << 24);
			}
			return word;
		}

		function incCounter(counter) {
			if ((counter[0] = incWord(counter[0])) === 0) {
				// encr_data in fileenc.c from  Dr Brian Gladman's counts only with DWORD j < 8
				counter[1] = incWord(counter[1]);
			}
			return counter;
		}

		var Encryptor = CTRGladman.Encryptor = CTRGladman.extend({
			processBlock: function (words, offset) {
				// Shortcuts
				var cipher = this._cipher
				var blockSize = cipher.blockSize;
				var iv = this._iv;
				var counter = this._counter;

				// Generate keystream
				if (iv) {
					counter = this._counter = iv.slice(0);

					// Remove IV for subsequent blocks
					this._iv = undefined;
				}

				incCounter(counter);

				var keystream = counter.slice(0);
				cipher.encryptBlock(keystream, 0);

				// Encrypt
				for (var i = 0; i < blockSize; i++) {
					words[offset + i] ^= keystream[i];
				}
			}
		});

		CTRGladman.Decryptor = Encryptor;

		return CTRGladman;
	}());




	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var StreamCipher = C_lib.StreamCipher;
		var C_algo = C.algo;

		// Reusable objects
		var S = [];
		var C_ = [];
		var G = [];

		/**
		 * Rabbit stream cipher algorithm
		 */
		var Rabbit = C_algo.Rabbit = StreamCipher.extend({
			_doReset: function () {
				// Shortcuts
				var K = this._key.words;
				var iv = this.cfg.iv;

				// Swap endian
				for (var i = 0; i < 4; i++) {
					K[i] = (((K[i] << 8) | (K[i] >>> 24)) & 0x00ff00ff) |
						(((K[i] << 24) | (K[i] >>> 8)) & 0xff00ff00);
				}

				// Generate initial state values
				var X = this._X = [
					K[0], (K[3] << 16) | (K[2] >>> 16),
					K[1], (K[0] << 16) | (K[3] >>> 16),
					K[2], (K[1] << 16) | (K[0] >>> 16),
					K[3], (K[2] << 16) | (K[1] >>> 16)
				];

				// Generate initial counter values
				var C = this._C = [
					(K[2] << 16) | (K[2] >>> 16), (K[0] & 0xffff0000) | (K[1] & 0x0000ffff),
					(K[3] << 16) | (K[3] >>> 16), (K[1] & 0xffff0000) | (K[2] & 0x0000ffff),
					(K[0] << 16) | (K[0] >>> 16), (K[2] & 0xffff0000) | (K[3] & 0x0000ffff),
					(K[1] << 16) | (K[1] >>> 16), (K[3] & 0xffff0000) | (K[0] & 0x0000ffff)
				];

				// Carry bit
				this._b = 0;

				// Iterate the system four times
				for (var i = 0; i < 4; i++) {
					nextState.call(this);
				}

				// Modify the counters
				for (var i = 0; i < 8; i++) {
					C[i] ^= X[(i + 4) & 7];
				}

				// IV setup
				if (iv) {
					// Shortcuts
					var IV = iv.words;
					var IV_0 = IV[0];
					var IV_1 = IV[1];

					// Generate four subvectors
					var i0 = (((IV_0 << 8) | (IV_0 >>> 24)) & 0x00ff00ff) | (((IV_0 << 24) | (IV_0 >>> 8)) & 0xff00ff00);
					var i2 = (((IV_1 << 8) | (IV_1 >>> 24)) & 0x00ff00ff) | (((IV_1 << 24) | (IV_1 >>> 8)) & 0xff00ff00);
					var i1 = (i0 >>> 16) | (i2 & 0xffff0000);
					var i3 = (i2 << 16) | (i0 & 0x0000ffff);

					// Modify counter values
					C[0] ^= i0;
					C[1] ^= i1;
					C[2] ^= i2;
					C[3] ^= i3;
					C[4] ^= i0;
					C[5] ^= i1;
					C[6] ^= i2;
					C[7] ^= i3;

					// Iterate the system four times
					for (var i = 0; i < 4; i++) {
						nextState.call(this);
					}
				}
			},

			_doProcessBlock: function (M, offset) {
				// Shortcut
				var X = this._X;

				// Iterate the system
				nextState.call(this);

				// Generate four keystream words
				S[0] = X[0] ^ (X[5] >>> 16) ^ (X[3] << 16);
				S[1] = X[2] ^ (X[7] >>> 16) ^ (X[5] << 16);
				S[2] = X[4] ^ (X[1] >>> 16) ^ (X[7] << 16);
				S[3] = X[6] ^ (X[3] >>> 16) ^ (X[1] << 16);

				for (var i = 0; i < 4; i++) {
					// Swap endian
					S[i] = (((S[i] << 8) | (S[i] >>> 24)) & 0x00ff00ff) |
						(((S[i] << 24) | (S[i] >>> 8)) & 0xff00ff00);

					// Encrypt
					M[offset + i] ^= S[i];
				}
			},

			blockSize: 128 / 32,

			ivSize: 64 / 32
		});

		function nextState() {
			// Shortcuts
			var X = this._X;
			var C = this._C;

			// Save old counter values
			for (var i = 0; i < 8; i++) {
				C_[i] = C[i];
			}

			// Calculate new counter values
			C[0] = (C[0] + 0x4d34d34d + this._b) | 0;
			C[1] = (C[1] + 0xd34d34d3 + ((C[0] >>> 0) < (C_[0] >>> 0) ? 1 : 0)) | 0;
			C[2] = (C[2] + 0x34d34d34 + ((C[1] >>> 0) < (C_[1] >>> 0) ? 1 : 0)) | 0;
			C[3] = (C[3] + 0x4d34d34d + ((C[2] >>> 0) < (C_[2] >>> 0) ? 1 : 0)) | 0;
			C[4] = (C[4] + 0xd34d34d3 + ((C[3] >>> 0) < (C_[3] >>> 0) ? 1 : 0)) | 0;
			C[5] = (C[5] + 0x34d34d34 + ((C[4] >>> 0) < (C_[4] >>> 0) ? 1 : 0)) | 0;
			C[6] = (C[6] + 0x4d34d34d + ((C[5] >>> 0) < (C_[5] >>> 0) ? 1 : 0)) | 0;
			C[7] = (C[7] + 0xd34d34d3 + ((C[6] >>> 0) < (C_[6] >>> 0) ? 1 : 0)) | 0;
			this._b = (C[7] >>> 0) < (C_[7] >>> 0) ? 1 : 0;

			// Calculate the g-values
			for (var i = 0; i < 8; i++) {
				var gx = X[i] + C[i];

				// Construct high and low argument for squaring
				var ga = gx & 0xffff;
				var gb = gx >>> 16;

				// Calculate high and low result of squaring
				var gh = ((((ga * ga) >>> 17) + ga * gb) >>> 15) + gb * gb;
				var gl = (((gx & 0xffff0000) * gx) | 0) + (((gx & 0x0000ffff) * gx) | 0);

				// High XOR low
				G[i] = gh ^ gl;
			}

			// Calculate new state values
			X[0] = (G[0] + ((G[7] << 16) | (G[7] >>> 16)) + ((G[6] << 16) | (G[6] >>> 16))) | 0;
			X[1] = (G[1] + ((G[0] << 8) | (G[0] >>> 24)) + G[7]) | 0;
			X[2] = (G[2] + ((G[1] << 16) | (G[1] >>> 16)) + ((G[0] << 16) | (G[0] >>> 16))) | 0;
			X[3] = (G[3] + ((G[2] << 8) | (G[2] >>> 24)) + G[1]) | 0;
			X[4] = (G[4] + ((G[3] << 16) | (G[3] >>> 16)) + ((G[2] << 16) | (G[2] >>> 16))) | 0;
			X[5] = (G[5] + ((G[4] << 8) | (G[4] >>> 24)) + G[3]) | 0;
			X[6] = (G[6] + ((G[5] << 16) | (G[5] >>> 16)) + ((G[4] << 16) | (G[4] >>> 16))) | 0;
			X[7] = (G[7] + ((G[6] << 8) | (G[6] >>> 24)) + G[5]) | 0;
		}

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.Rabbit.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.Rabbit.decrypt(ciphertext, key, cfg);
		 */
		C.Rabbit = StreamCipher._createHelper(Rabbit);
	}());


	/**
	 * Counter block mode.
	 */
	CryptoJS.mode.CTR = (function () {
		var CTR = CryptoJS.lib.BlockCipherMode.extend();

		var Encryptor = CTR.Encryptor = CTR.extend({
			processBlock: function (words, offset) {
				// Shortcuts
				var cipher = this._cipher
				var blockSize = cipher.blockSize;
				var iv = this._iv;
				var counter = this._counter;

				// Generate keystream
				if (iv) {
					counter = this._counter = iv.slice(0);

					// Remove IV for subsequent blocks
					this._iv = undefined;
				}
				var keystream = counter.slice(0);
				cipher.encryptBlock(keystream, 0);

				// Increment counter
				counter[blockSize - 1] = (counter[blockSize - 1] + 1) | 0

				// Encrypt
				for (var i = 0; i < blockSize; i++) {
					words[offset + i] ^= keystream[i];
				}
			}
		});

		CTR.Decryptor = Encryptor;

		return CTR;
	}());


	(function () {
		// Shortcuts
		var C = CryptoJS;
		var C_lib = C.lib;
		var StreamCipher = C_lib.StreamCipher;
		var C_algo = C.algo;

		// Reusable objects
		var S = [];
		var C_ = [];
		var G = [];

		/**
		 * Rabbit stream cipher algorithm.
		 *
		 * This is a legacy version that neglected to convert the key to little-endian.
		 * This error doesn't affect the cipher's security,
		 * but it does affect its compatibility with other implementations.
		 */
		var RabbitLegacy = C_algo.RabbitLegacy = StreamCipher.extend({
			_doReset: function () {
				// Shortcuts
				var K = this._key.words;
				var iv = this.cfg.iv;

				// Generate initial state values
				var X = this._X = [
					K[0], (K[3] << 16) | (K[2] >>> 16),
					K[1], (K[0] << 16) | (K[3] >>> 16),
					K[2], (K[1] << 16) | (K[0] >>> 16),
					K[3], (K[2] << 16) | (K[1] >>> 16)
				];

				// Generate initial counter values
				var C = this._C = [
					(K[2] << 16) | (K[2] >>> 16), (K[0] & 0xffff0000) | (K[1] & 0x0000ffff),
					(K[3] << 16) | (K[3] >>> 16), (K[1] & 0xffff0000) | (K[2] & 0x0000ffff),
					(K[0] << 16) | (K[0] >>> 16), (K[2] & 0xffff0000) | (K[3] & 0x0000ffff),
					(K[1] << 16) | (K[1] >>> 16), (K[3] & 0xffff0000) | (K[0] & 0x0000ffff)
				];

				// Carry bit
				this._b = 0;

				// Iterate the system four times
				for (var i = 0; i < 4; i++) {
					nextState.call(this);
				}

				// Modify the counters
				for (var i = 0; i < 8; i++) {
					C[i] ^= X[(i + 4) & 7];
				}

				// IV setup
				if (iv) {
					// Shortcuts
					var IV = iv.words;
					var IV_0 = IV[0];
					var IV_1 = IV[1];

					// Generate four subvectors
					var i0 = (((IV_0 << 8) | (IV_0 >>> 24)) & 0x00ff00ff) | (((IV_0 << 24) | (IV_0 >>> 8)) & 0xff00ff00);
					var i2 = (((IV_1 << 8) | (IV_1 >>> 24)) & 0x00ff00ff) | (((IV_1 << 24) | (IV_1 >>> 8)) & 0xff00ff00);
					var i1 = (i0 >>> 16) | (i2 & 0xffff0000);
					var i3 = (i2 << 16) | (i0 & 0x0000ffff);

					// Modify counter values
					C[0] ^= i0;
					C[1] ^= i1;
					C[2] ^= i2;
					C[3] ^= i3;
					C[4] ^= i0;
					C[5] ^= i1;
					C[6] ^= i2;
					C[7] ^= i3;

					// Iterate the system four times
					for (var i = 0; i < 4; i++) {
						nextState.call(this);
					}
				}
			},

			_doProcessBlock: function (M, offset) {
				// Shortcut
				var X = this._X;

				// Iterate the system
				nextState.call(this);

				// Generate four keystream words
				S[0] = X[0] ^ (X[5] >>> 16) ^ (X[3] << 16);
				S[1] = X[2] ^ (X[7] >>> 16) ^ (X[5] << 16);
				S[2] = X[4] ^ (X[1] >>> 16) ^ (X[7] << 16);
				S[3] = X[6] ^ (X[3] >>> 16) ^ (X[1] << 16);

				for (var i = 0; i < 4; i++) {
					// Swap endian
					S[i] = (((S[i] << 8) | (S[i] >>> 24)) & 0x00ff00ff) |
						(((S[i] << 24) | (S[i] >>> 8)) & 0xff00ff00);

					// Encrypt
					M[offset + i] ^= S[i];
				}
			},

			blockSize: 128 / 32,

			ivSize: 64 / 32
		});

		function nextState() {
			// Shortcuts
			var X = this._X;
			var C = this._C;

			// Save old counter values
			for (var i = 0; i < 8; i++) {
				C_[i] = C[i];
			}

			// Calculate new counter values
			C[0] = (C[0] + 0x4d34d34d + this._b) | 0;
			C[1] = (C[1] + 0xd34d34d3 + ((C[0] >>> 0) < (C_[0] >>> 0) ? 1 : 0)) | 0;
			C[2] = (C[2] + 0x34d34d34 + ((C[1] >>> 0) < (C_[1] >>> 0) ? 1 : 0)) | 0;
			C[3] = (C[3] + 0x4d34d34d + ((C[2] >>> 0) < (C_[2] >>> 0) ? 1 : 0)) | 0;
			C[4] = (C[4] + 0xd34d34d3 + ((C[3] >>> 0) < (C_[3] >>> 0) ? 1 : 0)) | 0;
			C[5] = (C[5] + 0x34d34d34 + ((C[4] >>> 0) < (C_[4] >>> 0) ? 1 : 0)) | 0;
			C[6] = (C[6] + 0x4d34d34d + ((C[5] >>> 0) < (C_[5] >>> 0) ? 1 : 0)) | 0;
			C[7] = (C[7] + 0xd34d34d3 + ((C[6] >>> 0) < (C_[6] >>> 0) ? 1 : 0)) | 0;
			this._b = (C[7] >>> 0) < (C_[7] >>> 0) ? 1 : 0;

			// Calculate the g-values
			for (var i = 0; i < 8; i++) {
				var gx = X[i] + C[i];

				// Construct high and low argument for squaring
				var ga = gx & 0xffff;
				var gb = gx >>> 16;

				// Calculate high and low result of squaring
				var gh = ((((ga * ga) >>> 17) + ga * gb) >>> 15) + gb * gb;
				var gl = (((gx & 0xffff0000) * gx) | 0) + (((gx & 0x0000ffff) * gx) | 0);

				// High XOR low
				G[i] = gh ^ gl;
			}

			// Calculate new state values
			X[0] = (G[0] + ((G[7] << 16) | (G[7] >>> 16)) + ((G[6] << 16) | (G[6] >>> 16))) | 0;
			X[1] = (G[1] + ((G[0] << 8) | (G[0] >>> 24)) + G[7]) | 0;
			X[2] = (G[2] + ((G[1] << 16) | (G[1] >>> 16)) + ((G[0] << 16) | (G[0] >>> 16))) | 0;
			X[3] = (G[3] + ((G[2] << 8) | (G[2] >>> 24)) + G[1]) | 0;
			X[4] = (G[4] + ((G[3] << 16) | (G[3] >>> 16)) + ((G[2] << 16) | (G[2] >>> 16))) | 0;
			X[5] = (G[5] + ((G[4] << 8) | (G[4] >>> 24)) + G[3]) | 0;
			X[6] = (G[6] + ((G[5] << 16) | (G[5] >>> 16)) + ((G[4] << 16) | (G[4] >>> 16))) | 0;
			X[7] = (G[7] + ((G[6] << 8) | (G[6] >>> 24)) + G[5]) | 0;
		}

		/**
		 * Shortcut functions to the cipher's object interface.
		 *
		 * @example
		 *
		 *     var ciphertext = CryptoJS.RabbitLegacy.encrypt(message, key, cfg);
		 *     var plaintext  = CryptoJS.RabbitLegacy.decrypt(ciphertext, key, cfg);
		 */
		C.RabbitLegacy = StreamCipher._createHelper(RabbitLegacy);
	}());


	/**
	 * Zero padding strategy.
	 */
	CryptoJS.pad.ZeroPadding = {
		pad: function (data, blockSize) {
			// Shortcut
			var blockSizeBytes = blockSize * 4;

			// Pad
			data.clamp();
			data.sigBytes += blockSizeBytes - ((data.sigBytes % blockSizeBytes) || blockSizeBytes);
		},

		unpad: function (data) {
			// Shortcut
			var dataWords = data.words;

			// Unpad
			var i = data.sigBytes - 1;
			for (var i = data.sigBytes - 1; i >= 0; i--) {
				if (((dataWords[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff)) {
					data.sigBytes = i + 1;
					break;
				}
			}
		}
	};


	return CryptoJS;

}));
/*
 SCRAMJS v1.0.1
 Copyright © 2016 Huawei Technologies Co., Ltd. All rights reserved.
 */
(function () {
	// Shortcuts
	var C = CryptoJS;
	var C_lib = C.lib;
	var WordArray = C_lib.WordArray;
	var C_algo = C.algo;

	var SHA2 = C_algo.SHA256;
	var HmacSHA2 = C.HmacSHA256;
	var Base = C_lib.Base;

	var SCRAM = C_algo.SCRAM = Base.extend({
		cfg: Base.extend({
			keySize: 8,
			hasher: SHA2,
			hmac: HmacSHA2
		}),

		init: function (cfg) {
			this.cfg = this.cfg.extend(cfg);
		},
		/**
		 *  return client nonce
		 */
		nonce: function () {
			lastNonce = WordArray.random(this.cfg.keySize * 4);
			return lastNonce;
		},
		/**
		 * pbkdf2
		 */
		saltedPassword: function (password, salt, iterations) {
			return CryptoJS.PBKDF2(password, salt, {
				keySize: this.cfg.keySize,
				iterations: iterations,
				hasher: this.cfg.hasher
			});
		},
		/**
		 *   ClientKey = HMAC(saltPwd, "Client Key")
		 */
		clientKey: function (saltPwd) {
			return this.cfg.hmac(saltPwd, "Client Key");
		},
		/**
		 *   ServerKey = HMAC(saltPwd, "Server Key")
		 */
		serverKey: function (saltPwd) {
			return this.cfg.hmac(saltPwd, "Server Key");
		},
		/**
		 *   StoredKey = HASH(ClientKey)
		 */
		storedKey: function (clientKey) {
			var hasher = this.cfg.hasher.create();
			hasher.update(clientKey);

			return hasher.finalize();
		},
		/**
		 *   Signature = HMAC(StoredKey, AuthMessage)
		 */
		signature: function (storedKey, authMessage) {
			return this.cfg.hmac(storedKey, authMessage);
		},
		/**
		 *   ClientProof = ClientKey ^ ClientSignature
		 */
		clientProof: function (password, salt, iterations, authMessage) {
			var spwd = this.saltedPassword(password, salt, iterations);
			var ckey = this.clientKey(spwd);
			var skey = this.storedKey(ckey);
			var csig = this.signature(skey, authMessage);

			for (var i = 0; i < ckey.sigBytes / 4; i += 1) {
				ckey.words[i] = ckey.words[i] ^ csig.words[i]
			}
			return ckey.toString();
		},
		/**
		 *   ServerProof = HMAC(ServerKey, AuthMessage)
		 */
		serverProof: function (password, salt, iterations, authMessage) {
			var spwd = this.saltedPassword(password, salt, iterations);
			var skey = this.serverKey(spwd);
			var sig = this.signature(skey, authMessage);
			return sig.toString();
		}
	});

	/**
	 *   var scram = CryptoJS.SCRAM();
	 */
	C.SCRAM = function (cfg) {
		return SCRAM.create(cfg);
	};
}());
/*! (c) Tom Wu | http://www-cs-students.stanford.edu/~tjw/jsbn/
 */
var b64map = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
var b64pad = "=";

function hex2b64(h) {
	var i;
	var c;
	var ret = "";
	for (i = 0; i + 3 <= h.length; i += 3) {
		c = parseInt(h.substring(i, i + 3), 16);
		ret += b64map.charAt(c >> 6) + b64map.charAt(c & 63);
	}
	if (i + 1 == h.length) {
		c = parseInt(h.substring(i, i + 1), 16);
		ret += b64map.charAt(c << 2);
	}
	else if (i + 2 == h.length) {
		c = parseInt(h.substring(i, i + 2), 16);
		ret += b64map.charAt(c >> 2) + b64map.charAt((c & 3) << 4);
	}
	if (b64pad) while ((ret.length & 3) > 0) ret += b64pad;
	return ret;
}

// convert a base64 string to hex
function b64tohex(s) {
	var ret = ""
	var i;
	var k = 0; // b64 state, 0-3
	var slop;
	var v;
	for (i = 0; i < s.length; ++i) {
		if (s.charAt(i) == b64pad) break;
		v = b64map.indexOf(s.charAt(i));
		if (v < 0) continue;
		if (k == 0) {
			ret += int2char(v >> 2);
			slop = v & 3;
			k = 1;
		}
		else if (k == 1) {
			ret += int2char((slop << 2) | (v >> 4));
			slop = v & 0xf;
			k = 2;
		}
		else if (k == 2) {
			ret += int2char(slop);
			ret += int2char(v >> 2);
			slop = v & 3;
			k = 3;
		}
		else {
			ret += int2char((slop << 2) | (v >> 4));
			ret += int2char(v & 0xf);
			k = 0;
		}
	}
	if (k == 1)
		ret += int2char(slop << 2);
	return ret;
}

// convert a base64 string to a byte/number array
function b64toBA(s) {
	//piggyback on b64tohex for now, optimize later
	var h = b64tohex(s);
	var i;
	var a = new Array();
	for (i = 0; 2 * i < h.length; ++i) {
		a[i] = parseInt(h.substring(2 * i, 2 * i + 2), 16);
	}
	return a;
}

!function (t, e) { "object" == typeof exports && "undefined" != typeof module ? module.exports = e() : "function" == typeof define && define.amd ? define(e) : t.ES6Promise = e() }(this, function () { "use strict"; function t(t) { var e = typeof t; return null !== t && ("object" === e || "function" === e) } function e(t) { return "function" == typeof t } function n(t) { W = t } function r(t) { z = t } function o() { return function () { return process.nextTick(a) } } function i() { return "undefined" != typeof U ? function () { U(a) } : c() } function s() { var t = 0, e = new H(a), n = document.createTextNode(""); return e.observe(n, { characterData: !0 }), function () { n.data = t = ++t % 2 } } function u() { var t = new MessageChannel; return t.port1.onmessage = a, function () { return t.port2.postMessage(0) } } function c() { var t = setTimeout; return function () { return t(a, 1) } } function a() { for (var t = 0; t < N; t += 2) { var e = Q[t], n = Q[t + 1]; e(n), Q[t] = void 0, Q[t + 1] = void 0 } N = 0 } function f() { try { var t = Function("return this")().require("vertx"); return U = t.runOnLoop || t.runOnContext, i() } catch (e) { return c() } } function l(t, e) { var n = this, r = new this.constructor(v); void 0 === r[V] && x(r); var o = n._state; if (o) { var i = arguments[o - 1]; z(function () { return T(o, r, i, n._result) }) } else j(n, r, t, e); return r } function h(t) { var e = this; if (t && "object" == typeof t && t.constructor === e) return t; var n = new e(v); return w(n, t), n } function v() { } function p() { return new TypeError("You cannot resolve a promise with itself") } function d() { return new TypeError("A promises callback cannot return that same promise.") } function _(t, e, n, r) { try { t.call(e, n, r) } catch (o) { return o } } function y(t, e, n) { z(function (t) { var r = !1, o = _(n, e, function (n) { r || (r = !0, e !== n ? w(t, n) : A(t, n)) }, function (e) { r || (r = !0, S(t, e)) }, "Settle: " + (t._label || " unknown promise")); !r && o && (r = !0, S(t, o)) }, t) } function m(t, e) { e._state === Z ? A(t, e._result) : e._state === $ ? S(t, e._result) : j(e, void 0, function (e) { return w(t, e) }, function (e) { return S(t, e) }) } function b(t, n, r) { n.constructor === t.constructor && r === l && n.constructor.resolve === h ? m(t, n) : void 0 === r ? A(t, n) : e(r) ? y(t, n, r) : A(t, n) } function w(e, n) { if (e === n) S(e, p()); else if (t(n)) { var r = void 0; try { r = n.then } catch (o) { return void S(e, o) } b(e, n, r) } else A(e, n) } function g(t) { t._onerror && t._onerror(t._result), E(t) } function A(t, e) { t._state === X && (t._result = e, t._state = Z, 0 !== t._subscribers.length && z(E, t)) } function S(t, e) { t._state === X && (t._state = $, t._result = e, z(g, t)) } function j(t, e, n, r) { var o = t._subscribers, i = o.length; t._onerror = null, o[i] = e, o[i + Z] = n, o[i + $] = r, 0 === i && t._state && z(E, t) } function E(t) { var e = t._subscribers, n = t._state; if (0 !== e.length) { for (var r = void 0, o = void 0, i = t._result, s = 0; s < e.length; s += 3)r = e[s], o = e[s + n], r ? T(n, r, o, i) : o(i); t._subscribers.length = 0 } } function T(t, n, r, o) { var i = e(r), s = void 0, u = void 0, c = !0; if (i) { try { s = r(o) } catch (a) { c = !1, u = a } if (n === s) return void S(n, d()) } else s = o; n._state !== X || (i && c ? w(n, s) : c === !1 ? S(n, u) : t === Z ? A(n, s) : t === $ && S(n, s)) } function M(t, e) { try { e(function (e) { w(t, e) }, function (e) { S(t, e) }) } catch (n) { S(t, n) } } function P() { return tt++ } function x(t) { t[V] = tt++, t._state = void 0, t._result = void 0, t._subscribers = [] } function C() { return new Error("Array Methods must be provided an Array") } function O(t) { return new et(this, t).promise } function k(t) { var e = this; return new e(L(t) ? function (n, r) { for (var o = t.length, i = 0; i < o; i++)e.resolve(t[i]).then(n, r) } : function (t, e) { return e(new TypeError("You must pass an array to race.")) }) } function F(t) { var e = this, n = new e(v); return S(n, t), n } function Y() { throw new TypeError("You must pass a resolver function as the first argument to the promise constructor") } function q() { throw new TypeError("Failed to construct 'Promise': Please use the 'new' operator, this object constructor cannot be called as a function.") } function D() { var t = void 0; if ("undefined" != typeof global) t = global; else if ("undefined" != typeof self) t = self; else try { t = Function("return this")() } catch (e) { throw new Error("polyfill failed because global object is unavailable in this environment") } var n = t.Promise; if (n) { var r = null; try { r = Object.prototype.toString.call(n.resolve()) } catch (e) { } if ("[object Promise]" === r && !n.cast) return } t.Promise = nt } var K = void 0; K = Array.isArray ? Array.isArray : function (t) { return "[object Array]" === Object.prototype.toString.call(t) }; var L = K, N = 0, U = void 0, W = void 0, z = function (t, e) { Q[N] = t, Q[N + 1] = e, N += 2, 2 === N && (W ? W(a) : R()) }, B = "undefined" != typeof window ? window : void 0, G = B || {}, H = G.MutationObserver || G.WebKitMutationObserver, I = "undefined" == typeof self && "undefined" != typeof process && "[object process]" === {}.toString.call(process), J = "undefined" != typeof Uint8ClampedArray && "undefined" != typeof importScripts && "undefined" != typeof MessageChannel, Q = new Array(1e3), R = void 0; R = I ? o() : H ? s() : J ? u() : void 0 === B && "function" == typeof require ? f() : c(); var V = Math.random().toString(36).substring(2), X = void 0, Z = 1, $ = 2, tt = 0, et = function () { function t(t, e) { this._instanceConstructor = t, this.promise = new t(v), this.promise[V] || x(this.promise), L(e) ? (this.length = e.length, this._remaining = e.length, this._result = new Array(this.length), 0 === this.length ? A(this.promise, this._result) : (this.length = this.length || 0, this._enumerate(e), 0 === this._remaining && A(this.promise, this._result))) : S(this.promise, C()) } return t.prototype._enumerate = function (t) { for (var e = 0; this._state === X && e < t.length; e++)this._eachEntry(t[e], e) }, t.prototype._eachEntry = function (t, e) { var n = this._instanceConstructor, r = n.resolve; if (r === h) { var o = void 0, i = void 0, s = !1; try { o = t.then } catch (u) { s = !0, i = u } if (o === l && t._state !== X) this._settledAt(t._state, e, t._result); else if ("function" != typeof o) this._remaining--, this._result[e] = t; else if (n === nt) { var c = new n(v); s ? S(c, i) : b(c, t, o), this._willSettleAt(c, e) } else this._willSettleAt(new n(function (e) { return e(t) }), e) } else this._willSettleAt(r(t), e) }, t.prototype._settledAt = function (t, e, n) { var r = this.promise; r._state === X && (this._remaining--, t === $ ? S(r, n) : this._result[e] = n), 0 === this._remaining && A(r, this._result) }, t.prototype._willSettleAt = function (t, e) { var n = this; j(t, void 0, function (t) { return n._settledAt(Z, e, t) }, function (t) { return n._settledAt($, e, t) }) }, t }(), nt = function () { function t(e) { this[V] = P(), this._result = this._state = void 0, this._subscribers = [], v !== e && ("function" != typeof e && Y(), this instanceof t ? M(this, e) : q()) } return t.prototype["catch"] = function (t) { return this.then(null, t) }, t.prototype["finally"] = function (t) { var n = this, r = n.constructor; return e(t) ? n.then(function (e) { return r.resolve(t()).then(function () { return e }) }, function (e) { return r.resolve(t()).then(function () { throw e }) }) : n.then(t, t) }, t }(); return nt.prototype.then = l, nt.all = O, nt.race = k, nt.resolve = h, nt.reject = F, nt._setScheduler = n, nt._setAsap = r, nt._asap = z, nt.polyfill = D, nt.Promise = nt, nt });
/* crypto-1.2.3.js (c) 2013-2020 Kenji Urushima | kjur.github.io/jsrsasign/license
 */
/*
 * crypto.js - Cryptographic Algorithm Provider class
 *
 * Copyright (c) 2013-2012 Kenji Urushima (kenji.urushima@gmail.com)
 *
 * This software is licensed under the terms of the MIT License.
 * https://kjur.github.io/jsrsasign/license
 *
 * The above copyright and license notice shall be 
 * included in all copies or substantial portions of the Software.
 */

/**
 * @fileOverview
 * @name crypto-1.1.js
 * @author Kenji Urushima kenji.urushima@gmail.com
 * @version 1.2.3 (2020-May-28)
 * @since jsrsasign 2.2
 * @license <a href="https://kjur.github.io/jsrsasign/license/">MIT License</a>
 */

/** 
 * kjur's class library name space
 * @name KJUR
 * @namespace kjur's class library name space
 */
if (typeof KJUR == "undefined" || !KJUR) KJUR = {};
/**
 * kjur's cryptographic algorithm provider library name space
 * <p>
 * This namespace privides following crytpgrahic classes.
 * <ul>
 * <li>{@link KJUR.crypto.MessageDigest} - Java JCE(cryptograhic extension) style MessageDigest class</li>
 * <li>{@link KJUR.crypto.Signature} - Java JCE(cryptograhic extension) style Signature class</li>
 * <li>{@link KJUR.crypto.Cipher} - class for encrypting and decrypting data</li>
 * <li>{@link KJUR.crypto.Util} - cryptographic utility functions and properties</li>
 * </ul>
 * NOTE: Please ignore method summary and document of this namespace. This caused by a bug of jsdoc2.
 * </p>
 * @name KJUR.crypto
 * @namespace
 */
if (typeof KJUR.crypto == "undefined" || !KJUR.crypto) KJUR.crypto = {};

/**
 * static object for cryptographic function utilities
 * @name KJUR.crypto.Util
 * @class static object for cryptographic function utilities
 * @property {Array} DIGESTINFOHEAD PKCS#1 DigestInfo heading hexadecimal bytes for each hash algorithms
 * @property {Array} DEFAULTPROVIDER associative array of default provider name for each hash and signature algorithms
 * @description
 */
KJUR.crypto.Util = new function () {
	this.DIGESTINFOHEAD = {
		'sha1': "3021300906052b0e03021a05000414",
		'sha224': "302d300d06096086480165030402040500041c",
		'sha256': "3031300d060960864801650304020105000420",
		'sha384': "3041300d060960864801650304020205000430",
		'sha512': "3051300d060960864801650304020305000440",
		'md2': "3020300c06082a864886f70d020205000410",
		'md5': "3020300c06082a864886f70d020505000410",
		'ripemd160': "3021300906052b2403020105000414",
	};

	/*
	 * @since crypto 1.1.1
	 */
	this.DEFAULTPROVIDER = {
		'md5': 'cryptojs',
		'sha1': 'cryptojs',
		'sha224': 'cryptojs',
		'sha256': 'cryptojs',
		'sha384': 'cryptojs',
		'sha512': 'cryptojs',
		'ripemd160': 'cryptojs',
		'hmacmd5': 'cryptojs',
		'hmacsha1': 'cryptojs',
		'hmacsha224': 'cryptojs',
		'hmacsha256': 'cryptojs',
		'hmacsha384': 'cryptojs',
		'hmacsha512': 'cryptojs',
		'hmacripemd160': 'cryptojs',

		'MD5withRSA': 'cryptojs/jsrsa',
		'SHA1withRSA': 'cryptojs/jsrsa',
		'SHA224withRSA': 'cryptojs/jsrsa',
		'SHA256withRSA': 'cryptojs/jsrsa',
		'SHA384withRSA': 'cryptojs/jsrsa',
		'SHA512withRSA': 'cryptojs/jsrsa',
		'RIPEMD160withRSA': 'cryptojs/jsrsa',

		'MD5withECDSA': 'cryptojs/jsrsa',
		'SHA1withECDSA': 'cryptojs/jsrsa',
		'SHA224withECDSA': 'cryptojs/jsrsa',
		'SHA256withECDSA': 'cryptojs/jsrsa',
		'SHA384withECDSA': 'cryptojs/jsrsa',
		'SHA512withECDSA': 'cryptojs/jsrsa',
		'RIPEMD160withECDSA': 'cryptojs/jsrsa',

		'SHA1withDSA': 'cryptojs/jsrsa',
		'SHA224withDSA': 'cryptojs/jsrsa',
		'SHA256withDSA': 'cryptojs/jsrsa',

		'MD5withRSAandMGF1': 'cryptojs/jsrsa',
		'SHA1withRSAandMGF1': 'cryptojs/jsrsa',
		'SHA224withRSAandMGF1': 'cryptojs/jsrsa',
		'SHA256withRSAandMGF1': 'cryptojs/jsrsa',
		'SHA384withRSAandMGF1': 'cryptojs/jsrsa',
		'SHA512withRSAandMGF1': 'cryptojs/jsrsa',
		'RIPEMD160withRSAandMGF1': 'cryptojs/jsrsa',
	};

	/*
	 * @since crypto 1.1.2
	 */
	this.CRYPTOJSMESSAGEDIGESTNAME = {
		'md5': CryptoJS.algo.MD5,
		'sha1': CryptoJS.algo.SHA1,
		'sha224': CryptoJS.algo.SHA224,
		'sha256': CryptoJS.algo.SHA256,
		'sha384': CryptoJS.algo.SHA384,
		'sha512': CryptoJS.algo.SHA512,
		'ripemd160': CryptoJS.algo.RIPEMD160
	};

	/**
	 * get hexadecimal DigestInfo
	 * @name getDigestInfoHex
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} hHash hexadecimal hash value
	 * @param {String} alg hash algorithm name (ex. 'sha1')
	 * @return {String} hexadecimal string DigestInfo ASN.1 structure
	 */
	this.getDigestInfoHex = function (hHash, alg) {
		if (typeof this.DIGESTINFOHEAD[alg] == "undefined")
			throw "alg not supported in Util.DIGESTINFOHEAD: " + alg;
		return this.DIGESTINFOHEAD[alg] + hHash;
	};

	/**
	 * get PKCS#1 padded hexadecimal DigestInfo
	 * @name getPaddedDigestInfoHex
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} hHash hexadecimal hash value of message to be signed
	 * @param {String} alg hash algorithm name (ex. 'sha1')
	 * @param {Integer} keySize key bit length (ex. 1024)
	 * @return {String} hexadecimal string of PKCS#1 padded DigestInfo
	 */
	this.getPaddedDigestInfoHex = function (hHash, alg, keySize) {
		var hDigestInfo = this.getDigestInfoHex(hHash, alg);
		var pmStrLen = keySize / 4; // minimum PM length

		if (hDigestInfo.length + 22 > pmStrLen) // len(0001+ff(*8)+00+hDigestInfo)=22
			throw "key is too short for SigAlg: keylen=" + keySize + "," + alg;

		var hHead = "0001";
		var hTail = "00" + hDigestInfo;
		var hMid = "";
		var fLen = pmStrLen - hHead.length - hTail.length;
		for (var i = 0; i < fLen; i += 2) {
			hMid += "ff";
		}
		var hPaddedMessage = hHead + hMid + hTail;
		return hPaddedMessage;
	};

	/**
	 * get hexadecimal hash of string with specified algorithm
	 * @name hashString
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} s raw input string to be hashed
	 * @param {String} alg hash algorithm name
	 * @return {String} hexadecimal string of hash value
	 * @since 1.1.1
	 */
	this.hashString = function (s, alg) {
		var md = new KJUR.crypto.MessageDigest({ 'alg': alg });
		return md.digestString(s);
	};

	/**
	 * get hexadecimal hash of hexadecimal string with specified algorithm
	 * @name hashHex
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} sHex input hexadecimal string to be hashed
	 * @param {String} alg hash algorithm name
	 * @return {String} hexadecimal string of hash value
	 * @since 1.1.1
	 */
	this.hashHex = function (sHex, alg) {
		var md = new KJUR.crypto.MessageDigest({ 'alg': alg });
		return md.digestHex(sHex);
	};

	/**
	 * get hexadecimal SHA1 hash of string
	 * @name sha1
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} s raw input string to be hashed
	 * @return {String} hexadecimal string of hash value
	 * @since 1.0.3
	 */
	this.sha1 = function (s) {
		return this.hashString(s, 'sha1');
	};

	/**
	 * get hexadecimal SHA256 hash of string
	 * @name sha256
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} s raw input string to be hashed
	 * @return {String} hexadecimal string of hash value
	 * @since 1.0.3
	 */
	this.sha256 = function (s) {
		return this.hashString(s, 'sha256');
	};

	this.sha256Hex = function (s) {
		return this.hashHex(s, 'sha256');
	};

	/**
	 * get hexadecimal SHA512 hash of string
	 * @name sha512
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {String} s raw input string to be hashed
	 * @return {String} hexadecimal string of hash value
	 * @since 1.0.3
	 */
	this.sha512 = function (s) {
		return this.hashString(s, 'sha512');
	};

	this.sha512Hex = function (s) {
		return this.hashHex(s, 'sha512');
	};

	/**
	 * check if key object (RSA/DSA/ECDSA) or not
	 * @name isKey
	 * @memberOf KJUR.crypto.Util
	 * @function
	 * @param {Object} obj any type argument to be checked
	 * @return {Boolean} true if this is key object otherwise false
	 * @since 1.0.3
	 */
	this.isKey = function (obj) {
		if (obj instanceof RSAKey ||
			obj instanceof KJUR.crypto.DSA ||
			obj instanceof KJUR.crypto.ECDSA) {
			return true;
		} else {
			return false;
		}
	};
};

/**
 * get hexadecimal MD5 hash of string
 * @name md5
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {String} s input string to be hashed
 * @return {String} hexadecimal string of hash value
 * @since 1.0.3
 * @example
 * Util.md5('aaa') &rarr; 47bce5c74f589f4867dbd57e9ca9f808
 */
KJUR.crypto.Util.md5 = function (s) {
	var md = new KJUR.crypto.MessageDigest({ 'alg': 'md5', 'prov': 'cryptojs' });
	return md.digestString(s);
};

/**
 * get hexadecimal RIPEMD160 hash of string
 * @name ripemd160
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {String} s input string to be hashed
 * @return {String} hexadecimal string of hash value
 * @since 1.0.3
 * @example
 * KJUR.crypto.Util.ripemd160("aaa") &rarr; 08889bd7b151aa174c21f33f59147fa65381edea
 */
KJUR.crypto.Util.ripemd160 = function (s) {
	var md = new KJUR.crypto.MessageDigest({ 'alg': 'ripemd160', 'prov': 'cryptojs' });
	return md.digestString(s);
};

// @since jsrsasign 7.0.0 crypto 1.1.11
KJUR.crypto.Util.SECURERANDOMGEN = new SecureRandom();

/**
 * get hexadecimal string of random value from with specified byte length<br/>
 * @name getRandomHexOfNbytes
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {Integer} n length of bytes of random
 * @return {String} hexadecimal string of random
 * @since jsrsasign 7.0.0 crypto 1.1.11
 * @example
 * KJUR.crypto.Util.getRandomHexOfNbytes(3) &rarr; "6314af", "000000" or "001fb4"
 * KJUR.crypto.Util.getRandomHexOfNbytes(128) &rarr; "8fbc..." in 1024bits 
 */
KJUR.crypto.Util.getRandomHexOfNbytes = function (n) {
	var ba = new Array(n);
	KJUR.crypto.Util.SECURERANDOMGEN.nextBytes(ba);
	return BAtohex(ba);
};

/**
 * get BigInteger object of random value from with specified byte length<br/>
 * @name getRandomBigIntegerOfNbytes
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {Integer} n length of bytes of random
 * @return {BigInteger} BigInteger object of specified random value
 * @since jsrsasign 7.0.0 crypto 1.1.11
 * @example
 * KJUR.crypto.Util.getRandomBigIntegerOfNbytes(3) &rarr; 6314af of BigInteger
 * KJUR.crypto.Util.getRandomBigIntegerOfNbytes(128) &rarr; 8fbc... of BigInteger
 */
KJUR.crypto.Util.getRandomBigIntegerOfNbytes = function (n) {
	return new BigInteger(KJUR.crypto.Util.getRandomHexOfNbytes(n), 16);
};

/**
 * get hexadecimal string of random value from with specified bit length<br/>
 * @name getRandomHexOfNbits
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {Integer} n length of bits of random
 * @return {String} hexadecimal string of random
 * @since jsrsasign 7.0.0 crypto 1.1.11
 * @example
 * KJUR.crypto.Util.getRandomHexOfNbits(24) &rarr; "6314af", "000000" or "001fb4"
 * KJUR.crypto.Util.getRandomHexOfNbits(1024) &rarr; "8fbc..." in 1024bits 
 */
KJUR.crypto.Util.getRandomHexOfNbits = function (n) {
	var n_remainder = n % 8;
	var n_quotient = (n - n_remainder) / 8;
	var ba = new Array(n_quotient + 1);
	KJUR.crypto.Util.SECURERANDOMGEN.nextBytes(ba);
	ba[0] = (((255 << n_remainder) & 255) ^ 255) & ba[0];
	return BAtohex(ba);
};

/**
 * get BigInteger object of random value from with specified bit length<br/>
 * @name getRandomBigIntegerOfNbits
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {Integer} n length of bits of random
 * @return {BigInteger} BigInteger object of specified random value
 * @since jsrsasign 7.0.0 crypto 1.1.11
 * @example
 * KJUR.crypto.Util.getRandomBigIntegerOfNbits(24) &rarr; 6314af of BigInteger
 * KJUR.crypto.Util.getRandomBigIntegerOfNbits(1024) &rarr; 8fbc... of BigInteger
 */
KJUR.crypto.Util.getRandomBigIntegerOfNbits = function (n) {
	return new BigInteger(KJUR.crypto.Util.getRandomHexOfNbits(n), 16);
};

/**
 * get BigInteger object of random value from zero to max value<br/>
 * @name getRandomBigIntegerZeroToMax
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {BigInteger} biMax max value of BigInteger object for random value
 * @return {BigInteger} BigInteger object of specified random value
 * @since jsrsasign 7.0.0 crypto 1.1.11
 * @description
 * This static method generates a BigInteger object with random value
 * greater than or equal to zero and smaller than or equal to biMax
 * (i.e. 0 &le; result &le; biMax).
 * @example
 * biMax = new BigInteger("3fa411...", 16);
 * KJUR.crypto.Util.getRandomBigIntegerZeroToMax(biMax) &rarr; 8fbc... of BigInteger
 */
KJUR.crypto.Util.getRandomBigIntegerZeroToMax = function (biMax) {
	var bitLenMax = biMax.bitLength();
	while (1) {
		var biRand = KJUR.crypto.Util.getRandomBigIntegerOfNbits(bitLenMax);
		if (biMax.compareTo(biRand) != -1) return biRand;
	}
};

/**
 * get BigInteger object of random value from min value to max value<br/>
 * @name getRandomBigIntegerMinToMax
 * @memberOf KJUR.crypto.Util
 * @function
 * @param {BigInteger} biMin min value of BigInteger object for random value
 * @param {BigInteger} biMax max value of BigInteger object for random value
 * @return {BigInteger} BigInteger object of specified random value
 * @since jsrsasign 7.0.0 crypto 1.1.11
 * @description
 * This static method generates a BigInteger object with random value
 * greater than or equal to biMin and smaller than or equal to biMax
 * (i.e. biMin &le; result &le; biMax).
 * @example
 * biMin = new BigInteger("2fa411...", 16);
 * biMax = new BigInteger("3fa411...", 16);
 * KJUR.crypto.Util.getRandomBigIntegerMinToMax(biMin, biMax) &rarr; 32f1... of BigInteger
 */
KJUR.crypto.Util.getRandomBigIntegerMinToMax = function (biMin, biMax) {
	var flagCompare = biMin.compareTo(biMax);
	if (flagCompare == 1) throw "biMin is greater than biMax";
	if (flagCompare == 0) return biMin;

	var biDiff = biMax.subtract(biMin);
	var biRand = KJUR.crypto.Util.getRandomBigIntegerZeroToMax(biDiff);
	return biRand.add(biMin);
};

// === Mac ===============================================================

/**
 * MessageDigest class which is very similar to java.security.MessageDigest class<br/>
 * @name KJUR.crypto.MessageDigest
 * @class MessageDigest class which is very similar to java.security.MessageDigest class
 * @param {Array} params parameters for constructor
 * @property {Array} HASHLENGTH static Array of resulted byte length of hash (ex. HASHLENGTH["sha1"] == 20)
 * @description
 * <br/>
 * Currently this supports following algorithm and providers combination:
 * <ul>
 * <li>md5 - cryptojs</li>
 * <li>sha1 - cryptojs</li>
 * <li>sha224 - cryptojs</li>
 * <li>sha256 - cryptojs</li>
 * <li>sha384 - cryptojs</li>
 * <li>sha512 - cryptojs</li>
 * <li>ripemd160 - cryptojs</li>
 * <li>sha256 - sjcl (NEW from crypto.js 1.0.4)</li>
 * </ul>
 * @example
 * // CryptoJS provider sample
 * var md = new KJUR.crypto.MessageDigest({alg: "sha1", prov: "cryptojs"});
 * md.updateString('aaa')
 * var mdHex = md.digest()
 *
 * // SJCL(Stanford JavaScript Crypto Library) provider sample
 * var md = new KJUR.crypto.MessageDigest({alg: "sha256", prov: "sjcl"}); // sjcl supports sha256 only
 * md.updateString('aaa')
 * var mdHex = md.digest()
 *
 * // HASHLENGTH property
 * KJUR.crypto.MessageDigest.HASHLENGTH['sha1'] &rarr 20
 * KJUR.crypto.MessageDigest.HASHLENGTH['sha512'] &rarr 64
 */
KJUR.crypto.MessageDigest = function (params) {
	var md = null;
	var algName = null;
	var provName = null;

	/**
	 * set hash algorithm and provider<br/>
	 * @name setAlgAndProvider
	 * @memberOf KJUR.crypto.MessageDigest#
	 * @function
	 * @param {String} alg hash algorithm name
	 * @param {String} prov provider name
	 * @description
	 * This methods set an algorithm and a cryptographic provider.<br/>
	 * Here is acceptable algorithm names ignoring cases and hyphens:
	 * <ul>
	 * <li>MD5</li>
	 * <li>SHA1</li>
	 * <li>SHA224</li>
	 * <li>SHA256</li>
	 * <li>SHA384</li>
	 * <li>SHA512</li>
	 * <li>RIPEMD160</li>
	 * </ul>
	 * NOTE: Since jsrsasign 6.2.0 crypto 1.1.10, this method ignores
	 * upper or lower cases. Also any hyphens (i.e. "-") will be ignored
	 * so that "SHA1" or "SHA-1" will be acceptable.
	 * @example
	 * // for SHA1
	 * md.setAlgAndProvider('sha1', 'cryptojs');
	 * md.setAlgAndProvider('SHA1');
	 * // for RIPEMD160
	 * md.setAlgAndProvider('ripemd160', 'cryptojs');
	 */
	this.setAlgAndProvider = function (alg, prov) {
		alg = KJUR.crypto.MessageDigest.getCanonicalAlgName(alg);

		if (alg !== null && prov === undefined) prov = KJUR.crypto.Util.DEFAULTPROVIDER[alg];

		// for cryptojs
		if (':md5:sha1:sha224:sha256:sha384:sha512:ripemd160:'.indexOf(alg) != -1 &&
			prov == 'cryptojs') {
			try {
				this.md = KJUR.crypto.Util.CRYPTOJSMESSAGEDIGESTNAME[alg].create();
			} catch (ex) {
				throw "setAlgAndProvider hash alg set fail alg=" + alg + "/" + ex;
			}
			this.updateString = function (str) {
				this.md.update(str);
			};
			this.updateHex = function (hex) {
				var wHex = CryptoJS.enc.Hex.parse(hex);
				this.md.update(wHex);
			};
			this.digest = function () {
				var hash = this.md.finalize();
				return hash.toString(CryptoJS.enc.Hex);
			};
			this.digestString = function (str) {
				this.updateString(str);
				return this.digest();
			};
			this.digestHex = function (hex) {
				this.updateHex(hex);
				return this.digest();
			};
		}
		if (':sha256:'.indexOf(alg) != -1 &&
			prov == 'sjcl') {
			try {
				this.md = new sjcl.hash.sha256();
			} catch (ex) {
				throw "setAlgAndProvider hash alg set fail alg=" + alg + "/" + ex;
			}
			this.updateString = function (str) {
				this.md.update(str);
			};
			this.updateHex = function (hex) {
				var baHex = sjcl.codec.hex.toBits(hex);
				this.md.update(baHex);
			};
			this.digest = function () {
				var hash = this.md.finalize();
				return sjcl.codec.hex.fromBits(hash);
			};
			this.digestString = function (str) {
				this.updateString(str);
				return this.digest();
			};
			this.digestHex = function (hex) {
				this.updateHex(hex);
				return this.digest();
			};
		}
	};

	/**
	 * update digest by specified string
	 * @name updateString
	 * @memberOf KJUR.crypto.MessageDigest#
	 * @function
	 * @param {String} str string to update
	 * @description
	 * @example
	 * md.updateString('New York');
	 */
	this.updateString = function (str) {
		throw "updateString(str) not supported for this alg/prov: " + this.algName + "/" + this.provName;
	};

	/**
	 * update digest by specified hexadecimal string
	 * @name updateHex
	 * @memberOf KJUR.crypto.MessageDigest#
	 * @function
	 * @param {String} hex hexadecimal string to update
	 * @description
	 * @example
	 * md.updateHex('0afe36');
	 */
	this.updateHex = function (hex) {
		throw "updateHex(hex) not supported for this alg/prov: " + this.algName + "/" + this.provName;
	};

	/**
	 * completes hash calculation and returns hash result
	 * @name digest
	 * @memberOf KJUR.crypto.MessageDigest#
	 * @function
	 * @description
	 * @example
	 * md.digest()
	 */
	this.digest = function () {
		throw "digest() not supported for this alg/prov: " + this.algName + "/" + this.provName;
	};

	/**
	 * performs final update on the digest using string, then completes the digest computation
	 * @name digestString
	 * @memberOf KJUR.crypto.MessageDigest#
	 * @function
	 * @param {String} str string to final update
	 * @description
	 * @example
	 * md.digestString('aaa')
	 */
	this.digestString = function (str) {
		throw "digestString(str) not supported for this alg/prov: " + this.algName + "/" + this.provName;
	};

	/**
	 * performs final update on the digest using hexadecimal string, then completes the digest computation
	 * @name digestHex
	 * @memberOf KJUR.crypto.MessageDigest#
	 * @function
	 * @param {String} hex hexadecimal string to final update
	 * @description
	 * @example
	 * md.digestHex('0f2abd')
	 */
	this.digestHex = function (hex) {
		throw "digestHex(hex) not supported for this alg/prov: " + this.algName + "/" + this.provName;
	};

	if (params !== undefined) {
		if (params['alg'] !== undefined) {
			this.algName = params['alg'];
			if (params['prov'] === undefined)
				this.provName = KJUR.crypto.Util.DEFAULTPROVIDER[this.algName];
			this.setAlgAndProvider(this.algName, this.provName);
		}
	}
};

/**
 * get canonical hash algorithm name<br/>
 * @name getCanonicalAlgName
 * @memberOf KJUR.crypto.MessageDigest
 * @function
 * @param {String} alg hash algorithm name (ex. MD5, SHA-1, SHA1, SHA512 et.al.)
 * @return {String} canonical hash algorithm name
 * @since jsrsasign 6.2.0 crypto 1.1.10
 * @description
 * This static method normalizes from any hash algorithm name such as
 * "SHA-1", "SHA1", "MD5", "sha512" to lower case name without hyphens
 * such as "sha1".
 * @example
 * KJUR.crypto.MessageDigest.getCanonicalAlgName("SHA-1") &rarr "sha1"
 * KJUR.crypto.MessageDigest.getCanonicalAlgName("MD5")   &rarr "md5"
 */
KJUR.crypto.MessageDigest.getCanonicalAlgName = function (alg) {
	if (typeof alg === "string") {
		alg = alg.toLowerCase();
		alg = alg.replace(/-/, '');
	}
	return alg;
};

/**
 * get resulted hash byte length for specified algorithm name<br/>
 * @name getHashLength
 * @memberOf KJUR.crypto.MessageDigest
 * @function
 * @param {String} alg non-canonicalized hash algorithm name (ex. MD5, SHA-1, SHA1, SHA512 et.al.)
 * @return {Integer} resulted hash byte length
 * @since jsrsasign 6.2.0 crypto 1.1.10
 * @description
 * This static method returns resulted byte length for specified algorithm name such as "SHA-1".
 * @example
 * KJUR.crypto.MessageDigest.getHashLength("SHA-1") &rarr 20
 * KJUR.crypto.MessageDigest.getHashLength("sha1") &rarr 20
 */
KJUR.crypto.MessageDigest.getHashLength = function (alg) {
	var MD = KJUR.crypto.MessageDigest
	var alg2 = MD.getCanonicalAlgName(alg);
	if (MD.HASHLENGTH[alg2] === undefined)
		throw "not supported algorithm: " + alg;
	return MD.HASHLENGTH[alg2];
};

// described in KJUR.crypto.MessageDigest class (since jsrsasign 6.2.0 crypto 1.1.10)
KJUR.crypto.MessageDigest.HASHLENGTH = {
	'md5': 16,
	'sha1': 20,
	'sha224': 28,
	'sha256': 32,
	'sha384': 48,
	'sha512': 64,
	'ripemd160': 20
};

// === Mac ===============================================================

/**
 * Mac(Message Authentication Code) class which is very similar to java.security.Mac class 
 * @name KJUR.crypto.Mac
 * @class Mac class which is very similar to java.security.Mac class
 * @param {Array} params parameters for constructor
 * @description
 * <br/>
 * Currently this supports following algorithm and providers combination:
 * <ul>
 * <li>hmacmd5 - cryptojs</li>
 * <li>hmacsha1 - cryptojs</li>
 * <li>hmacsha224 - cryptojs</li>
 * <li>hmacsha256 - cryptojs</li>
 * <li>hmacsha384 - cryptojs</li>
 * <li>hmacsha512 - cryptojs</li>
 * </ul>
 * NOTE: HmacSHA224 and HmacSHA384 issue was fixed since jsrsasign 4.1.4.
 * Please use 'ext/cryptojs-312-core-fix*.js' instead of 'core.js' of original CryptoJS
 * to avoid those issue.
 * <br/>
 * NOTE2: Hmac signature bug was fixed in jsrsasign 4.9.0 by providing CryptoJS
 * bug workaround.
 * <br/>
 * Please see {@link KJUR.crypto.Mac.setPassword}, how to provide password
 * in various ways in detail.
 * @example
 * var mac = new KJUR.crypto.Mac({alg: "HmacSHA1", "pass": "pass"});
 * mac.updateString('aaa')
 * var macHex = mac.doFinal()
 *
 * // other password representation 
 * var mac = new KJUR.crypto.Mac({alg: "HmacSHA256", "pass": {"hex":  "6161"}});
 * var mac = new KJUR.crypto.Mac({alg: "HmacSHA256", "pass": {"utf8": "aa"}});
 * var mac = new KJUR.crypto.Mac({alg: "HmacSHA256", "pass": {"rstr": "\x61\x61"}});
 * var mac = new KJUR.crypto.Mac({alg: "HmacSHA256", "pass": {"b64":  "Mi02/+...a=="}});
 * var mac = new KJUR.crypto.Mac({alg: "HmacSHA256", "pass": {"b64u": "Mi02_-...a"}});
 */
KJUR.crypto.Mac = function (params) {
	var mac = null;
	var pass = null;
	var algName = null;
	var provName = null;
	var algProv = null;

	this.setAlgAndProvider = function (alg, prov) {
		alg = alg.toLowerCase();

		if (alg == null) alg = "hmacsha1";

		alg = alg.toLowerCase();
		if (alg.substr(0, 4) != "hmac") {
			throw "setAlgAndProvider unsupported HMAC alg: " + alg;
		}

		if (prov === undefined) prov = KJUR.crypto.Util.DEFAULTPROVIDER[alg];
		this.algProv = alg + "/" + prov;

		var hashAlg = alg.substr(4);

		// for cryptojs
		if (':md5:sha1:sha224:sha256:sha384:sha512:ripemd160:'.indexOf(hashAlg) != -1 &&
			prov == 'cryptojs') {
			try {
				var mdObj = KJUR.crypto.Util.CRYPTOJSMESSAGEDIGESTNAME[hashAlg];
				this.mac = CryptoJS.algo.HMAC.create(mdObj, this.pass);
			} catch (ex) {
				throw "setAlgAndProvider hash alg set fail hashAlg=" + hashAlg + "/" + ex;
			}
			this.updateString = function (str) {
				this.mac.update(str);
			};
			this.updateHex = function (hex) {
				var wHex = CryptoJS.enc.Hex.parse(hex);
				this.mac.update(wHex);
			};
			this.doFinal = function () {
				var hash = this.mac.finalize();
				return hash.toString(CryptoJS.enc.Hex);
			};
			this.doFinalString = function (str) {
				this.updateString(str);
				return this.doFinal();
			};
			this.doFinalHex = function (hex) {
				this.updateHex(hex);
				return this.doFinal();
			};
		}
	};

	/**
	 * update digest by specified string
	 * @name updateString
	 * @memberOf KJUR.crypto.Mac#
	 * @function
	 * @param {String} str string to update
	 * @description
	 * @example
	 * mac.updateString('New York');
	 */
	this.updateString = function (str) {
		throw "updateString(str) not supported for this alg/prov: " + this.algProv;
	};

	/**
	 * update digest by specified hexadecimal string
	 * @name updateHex
	 * @memberOf KJUR.crypto.Mac#
	 * @function
	 * @param {String} hex hexadecimal string to update
	 * @description
	 * @example
	 * mac.updateHex('0afe36');
	 */
	this.updateHex = function (hex) {
		throw "updateHex(hex) not supported for this alg/prov: " + this.algProv;
	};

	/**
	 * completes hash calculation and returns hash result
	 * @name doFinal
	 * @memberOf KJUR.crypto.Mac#
	 * @function
	 * @description
	 * @example
	 * mac.digest()
	 */
	this.doFinal = function () {
		throw "digest() not supported for this alg/prov: " + this.algProv;
	};

	/**
	 * performs final update on the digest using string, then completes the digest computation
	 * @name doFinalString
	 * @memberOf KJUR.crypto.Mac#
	 * @function
	 * @param {String} str string to final update
	 * @description
	 * @example
	 * mac.digestString('aaa')
	 */
	this.doFinalString = function (str) {
		throw "digestString(str) not supported for this alg/prov: " + this.algProv;
	};

	/**
	 * performs final update on the digest using hexadecimal string, 
	 * then completes the digest computation
	 * @name doFinalHex
	 * @memberOf KJUR.crypto.Mac#
	 * @function
	 * @param {String} hex hexadecimal string to final update
	 * @description
	 * @example
	 * mac.digestHex('0f2abd')
	 */
	this.doFinalHex = function (hex) {
		throw "digestHex(hex) not supported for this alg/prov: " + this.algProv;
	};

	/**
	 * set password for Mac
	 * @name setPassword
	 * @memberOf KJUR.crypto.Mac#
	 * @function
	 * @param {Object} pass password for Mac
	 * @since crypto 1.1.7 jsrsasign 4.9.0
	 * @description
	 * This method will set password for (H)Mac internally.
	 * Argument 'pass' can be specified as following:
	 * <ul>
	 * <li>even length string of 0..9, a..f or A-F: implicitly specified as hexadecimal string</li>
	 * <li>not above string: implicitly specified as raw string</li>
	 * <li>{rstr: "\x65\x70"}: explicitly specified as raw string</li>
	 * <li>{hex: "6570"}: explicitly specified as hexacedimal string</li>
	 * <li>{utf8: "秘密"}: explicitly specified as UTF8 string</li>
	 * <li>{b64: "Mi78..=="}: explicitly specified as Base64 string</li>
	 * <li>{b64u: "Mi7-_"}: explicitly specified as Base64URL string</li>
	 * </ul>
	 * It is *STRONGLY RECOMMENDED* that explicit representation of password argument
	 * to avoid ambiguity. For example string  "6161" can mean a string "6161" or 
	 * a hexadecimal string of "aa" (i.e. \x61\x61).
	 * @example
	 * mac = KJUR.crypto.Mac({'alg': 'hmacsha256'});
	 * // set password by implicit raw string
	 * mac.setPassword("\x65\x70\xb9\x0b");
	 * mac.setPassword("password");
	 * // set password by implicit hexadecimal string
	 * mac.setPassword("6570b90b");
	 * mac.setPassword("6570B90B");
	 * // set password by explicit raw string
	 * mac.setPassword({"rstr": "\x65\x70\xb9\x0b"});
	 * // set password by explicit hexadecimal string
	 * mac.setPassword({"hex": "6570b90b"});
	 * // set password by explicit utf8 string
	 * mac.setPassword({"utf8": "passwordパスワード");
	 * // set password by explicit Base64 string
	 * mac.setPassword({"b64": "Mb+c3f/=="});
	 * // set password by explicit Base64URL string
	 * mac.setPassword({"b64u": "Mb-c3f_"});
	 */
	this.setPassword = function (pass) {
		// internal this.pass shall be CryptoJS DWord Object for CryptoJS bug
		// work around. CrytoJS HMac password can be passed by
		// raw string as described in the manual however it doesn't
		// work properly in some case. If password was passed
		// by CryptoJS DWord which is not described in the manual
		// it seems to work. (fixed since crypto 1.1.7)

		if (typeof pass == 'string') {
			var hPass = pass;
			if (pass.length % 2 == 1 || !pass.match(/^[0-9A-Fa-f]+$/)) { // raw str
				hPass = rstrtohex(pass);
			}
			this.pass = CryptoJS.enc.Hex.parse(hPass);
			return;
		}

		if (typeof pass != 'object')
			throw "KJUR.crypto.Mac unsupported password type: " + pass;

		var hPass = null;
		if (pass.hex !== undefined) {
			if (pass.hex.length % 2 != 0 || !pass.hex.match(/^[0-9A-Fa-f]+$/))
				throw "Mac: wrong hex password: " + pass.hex;
			hPass = pass.hex;
		}
		if (pass.utf8 !== undefined) hPass = utf8tohex(pass.utf8);
		if (pass.rstr !== undefined) hPass = rstrtohex(pass.rstr);
		if (pass.b64 !== undefined) hPass = b64tohex(pass.b64);
		if (pass.b64u !== undefined) hPass = b64utohex(pass.b64u);

		if (hPass == null)
			throw "KJUR.crypto.Mac unsupported password type: " + pass;

		this.pass = CryptoJS.enc.Hex.parse(hPass);
	};

	if (params !== undefined) {
		if (params.pass !== undefined) {
			this.setPassword(params.pass);
		}
		if (params.alg !== undefined) {
			this.algName = params.alg;
			if (params['prov'] === undefined)
				this.provName = KJUR.crypto.Util.DEFAULTPROVIDER[this.algName];
			this.setAlgAndProvider(this.algName, this.provName);
		}
	}
};

// ====== Signature class =========================================================
/**
 * Signature class which is very similar to java.security.Signature class
 * @name KJUR.crypto.Signature
 * @class Signature class which is very similar to java.security.Signature class
 * @param {Array} params parameters for constructor
 * @property {String} state Current state of this signature object whether 'SIGN', 'VERIFY' or null
 * @description
 * <br/>
 * As for params of constructor's argument, it can be specify following attributes:
 * <ul>
 * <li>alg - signature algorithm name (ex. {MD5,SHA1,SHA224,SHA256,SHA384,SHA512,RIPEMD160}with{RSA,ECDSA,DSA})</li>
 * <li>provider - currently 'cryptojs/jsrsa' only</li>
 * </ul>
 * <h4>SUPPORTED ALGORITHMS AND PROVIDERS</h4>
 * This Signature class supports following signature algorithm and provider names:
 * <ul>
 * <li>MD5withRSA - cryptojs/jsrsa</li>
 * <li>SHA1withRSA - cryptojs/jsrsa</li>
 * <li>SHA224withRSA - cryptojs/jsrsa</li>
 * <li>SHA256withRSA - cryptojs/jsrsa</li>
 * <li>SHA384withRSA - cryptojs/jsrsa</li>
 * <li>SHA512withRSA - cryptojs/jsrsa</li>
 * <li>RIPEMD160withRSA - cryptojs/jsrsa</li>
 * <li>MD5withECDSA - cryptojs/jsrsa</li>
 * <li>SHA1withECDSA - cryptojs/jsrsa</li>
 * <li>SHA224withECDSA - cryptojs/jsrsa</li>
 * <li>SHA256withECDSA - cryptojs/jsrsa</li>
 * <li>SHA384withECDSA - cryptojs/jsrsa</li>
 * <li>SHA512withECDSA - cryptojs/jsrsa</li>
 * <li>RIPEMD160withECDSA - cryptojs/jsrsa</li>
 * <li>MD5withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>SHA1withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>SHA224withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>SHA256withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>SHA384withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>SHA512withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>RIPEMD160withRSAandMGF1 - cryptojs/jsrsa</li>
 * <li>SHA1withDSA - cryptojs/jsrsa</li>
 * <li>SHA224withDSA - cryptojs/jsrsa</li>
 * <li>SHA256withDSA - cryptojs/jsrsa</li>
 * </ul>
 * Here are supported elliptic cryptographic curve names and their aliases for ECDSA:
 * <ul>
 * <li>secp256k1</li>
 * <li>secp256r1, NIST P-256, P-256, prime256v1</li>
 * <li>secp384r1, NIST P-384, P-384</li>
 * </ul>
 * NOTE1: DSA signing algorithm is also supported since crypto 1.1.5.
 * <h4>EXAMPLES</h4>
 * @example
 * // RSA signature generation
 * var sig = new KJUR.crypto.Signature({"alg": "SHA1withRSA"});
 * sig.init(prvKeyPEM);
 * sig.updateString('aaa');
 * var hSigVal = sig.sign();
 *
 * // DSA signature validation
 * var sig2 = new KJUR.crypto.Signature({"alg": "SHA1withDSA"});
 * sig2.init(certPEM);
 * sig.updateString('aaa');
 * var isValid = sig2.verify(hSigVal);
 * 
 * // ECDSA signing
 * var sig = new KJUR.crypto.Signature({'alg':'SHA1withECDSA'});
 * sig.init(prvKeyPEM);
 * sig.updateString('aaa');
 * var sigValueHex = sig.sign();
 *
 * // ECDSA verifying
 * var sig2 = new KJUR.crypto.Signature({'alg':'SHA1withECDSA'});
 * sig.init(certPEM);
 * sig.updateString('aaa');
 * var isValid = sig.verify(sigValueHex);
 */
KJUR.crypto.Signature = function (params) {
	var prvKey = null; // RSAKey/KJUR.crypto.{ECDSA,DSA} object for signing
	var pubKey = null; // RSAKey/KJUR.crypto.{ECDSA,DSA} object for verifying

	var md = null; // KJUR.crypto.MessageDigest object
	var sig = null;
	var algName = null;
	var provName = null;
	var algProvName = null;
	var mdAlgName = null;
	var pubkeyAlgName = null;	// rsa,ecdsa,rsaandmgf1(=rsapss)
	var state = null;
	var pssSaltLen = -1;
	var initParams = null;

	var sHashHex = null; // hex hash value for hex
	var hDigestInfo = null;
	var hPaddedDigestInfo = null;
	var hSign = null;

	this._setAlgNames = function () {
		var matchResult = this.algName.match(/^(.+)with(.+)$/);
		if (matchResult) {
			this.mdAlgName = matchResult[1].toLowerCase();
			this.pubkeyAlgName = matchResult[2].toLowerCase();
		}
	};

	this._zeroPaddingOfSignature = function (hex, bitLength) {
		var s = "";
		var nZero = bitLength / 4 - hex.length;
		for (var i = 0; i < nZero; i++) {
			s = s + "0";
		}
		return s + hex;
	};

	/**
	 * set signature algorithm and provider
	 * @name setAlgAndProvider
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {String} alg signature algorithm name
	 * @param {String} prov provider name
	 * @description
	 * @example
	 * md.setAlgAndProvider('SHA1withRSA', 'cryptojs/jsrsa');
	 */
	this.setAlgAndProvider = function (alg, prov) {
		this._setAlgNames();
		if (prov != 'cryptojs/jsrsa')
			throw "provider not supported: " + prov;

		if (':md5:sha1:sha224:sha256:sha384:sha512:ripemd160:'.indexOf(this.mdAlgName) != -1) {
			try {
				this.md = new KJUR.crypto.MessageDigest({ 'alg': this.mdAlgName });
			} catch (ex) {
				throw "setAlgAndProvider hash alg set fail alg=" +
				this.mdAlgName + "/" + ex;
			}

			this.init = function (keyparam, pass) {
				var keyObj = null;
				try {
					if (pass === undefined) {
						keyObj = KEYUTIL.getKey(keyparam);
					} else {
						keyObj = KEYUTIL.getKey(keyparam, pass);
					}
				} catch (ex) {
					throw "init failed:" + ex;
				}

				if (keyObj.isPrivate === true) {
					this.prvKey = keyObj;
					this.state = "SIGN";
				} else if (keyObj.isPublic === true) {
					this.pubKey = keyObj;
					this.state = "VERIFY";
				} else {
					throw "init failed.:" + keyObj;
				}
			};

			this.updateString = function (str) {
				this.md.updateString(str);
			};

			this.updateHex = function (hex) {
				this.md.updateHex(hex);
			};

			this.sign = function () {
				this.sHashHex = this.md.digest();
				// hex parameter EC public key
				if (this.prvKey === undefined &&
					this.ecprvhex !== undefined &&
					this.eccurvename !== undefined &&
					KJUR.crypto.ECDSA !== undefined) {
					this.prvKey = new KJUR.crypto.ECDSA({
						'curve': this.eccurvename,
						prv: this.ecprvhex
					});
				}

				// RSAPSS
				if (this.prvKey instanceof RSAKey &&
					this.pubkeyAlgName === "rsaandmgf1") {
					this.hSign = this.prvKey.signWithMessageHashPSS(this.sHashHex,
						this.mdAlgName,
						this.pssSaltLen);
					// RSA
				} else if (this.prvKey instanceof RSAKey &&
					this.pubkeyAlgName === "rsa") {
					this.hSign = this.prvKey.signWithMessageHash(this.sHashHex,
						this.mdAlgName);
					// ECDSA
				} else if (this.prvKey instanceof KJUR.crypto.ECDSA) {
					this.hSign = this.prvKey.signWithMessageHash(this.sHashHex);
					// DSA
				} else if (this.prvKey instanceof KJUR.crypto.DSA) {
					this.hSign = this.prvKey.signWithMessageHash(this.sHashHex);
				} else {
					throw "Signature: unsupported private key alg: " + this.pubkeyAlgName;
				}
				return this.hSign;
			};
			this.signString = function (str) {
				this.updateString(str);
				return this.sign();
			};
			this.signHex = function (hex) {
				this.updateHex(hex);
				return this.sign();
			};
			this.verify = function (hSigVal) {
				this.sHashHex = this.md.digest();
				// hex parameter EC public key
				if (this.pubKey === undefined &&
					this.ecpubhex !== undefined &&
					this.eccurvename !== undefined &&
					KJUR.crypto.ECDSA !== undefined) {
					this.pubKey = new KJUR.crypto.ECDSA({
						curve: this.eccurvename,
						pub: this.ecpubhex
					});
				}

				// RSAPSS
				if (this.pubKey instanceof RSAKey &&
					this.pubkeyAlgName === "rsaandmgf1") {
					return this.pubKey.verifyWithMessageHashPSS(this.sHashHex, hSigVal,
						this.mdAlgName,
						this.pssSaltLen);
					// RSA
				} else if (this.pubKey instanceof RSAKey &&
					this.pubkeyAlgName === "rsa") {
					return this.pubKey.verifyWithMessageHash(this.sHashHex, hSigVal);
					// ECDSA
				} else if (KJUR.crypto.ECDSA !== undefined &&
					this.pubKey instanceof KJUR.crypto.ECDSA) {
					return this.pubKey.verifyWithMessageHash(this.sHashHex, hSigVal);
					// DSA
				} else if (KJUR.crypto.DSA !== undefined &&
					this.pubKey instanceof KJUR.crypto.DSA) {
					return this.pubKey.verifyWithMessageHash(this.sHashHex, hSigVal);
				} else {
					throw "Signature: unsupported public key alg: " + this.pubkeyAlgName;
				}
			};
		}
	};

	/**
	 * Initialize this object for signing or verifying depends on key
	 * @name init
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {Object} key specifying public or private key as plain/encrypted PKCS#5/8 PEM file, certificate PEM or {@link RSAKey}, {@link KJUR.crypto.DSA} or {@link KJUR.crypto.ECDSA} object
	 * @param {String} pass (OPTION) passcode for encrypted private key
	 * @since crypto 1.1.3
	 * @description
	 * This method is very useful initialize method for Signature class since
	 * you just specify key then this method will automatically initialize it
	 * using {@link KEYUTIL.getKey} method.
	 * As for 'key',  following argument type are supported:
	 * <h5>signing</h5>
	 * <ul>
	 * <li>PEM formatted PKCS#8 encrypted RSA/ECDSA private key concluding "BEGIN ENCRYPTED PRIVATE KEY"</li>
	 * <li>PEM formatted PKCS#5 encrypted RSA/DSA private key concluding "BEGIN RSA/DSA PRIVATE KEY" and ",ENCRYPTED"</li>
	 * <li>PEM formatted PKCS#8 plain RSA/ECDSA private key concluding "BEGIN PRIVATE KEY"</li>
	 * <li>PEM formatted PKCS#5 plain RSA/DSA private key concluding "BEGIN RSA/DSA PRIVATE KEY" without ",ENCRYPTED"</li>
	 * <li>RSAKey object of private key</li>
	 * <li>KJUR.crypto.ECDSA object of private key</li>
	 * <li>KJUR.crypto.DSA object of private key</li>
	 * </ul>
	 * <h5>verification</h5>
	 * <ul>
	 * <li>PEM formatted PKCS#8 RSA/EC/DSA public key concluding "BEGIN PUBLIC KEY"</li>
	 * <li>PEM formatted X.509 certificate with RSA/EC/DSA public key concluding
	 *     "BEGIN CERTIFICATE", "BEGIN X509 CERTIFICATE" or "BEGIN TRUSTED CERTIFICATE".</li>
	 * <li>RSAKey object of public key</li>
	 * <li>KJUR.crypto.ECDSA object of public key</li>
	 * <li>KJUR.crypto.DSA object of public key</li>
	 * </ul>
	 * @example
	 * sig.init(sCertPEM)
	 */
	this.init = function (key, pass) {
		throw "init(key, pass) not supported for this alg:prov=" +
		this.algProvName;
	};

	/**
	 * Updates the data to be signed or verified by a string
	 * @name updateString
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {String} str string to use for the update
	 * @description
	 * @example
	 * sig.updateString('aaa')
	 */
	this.updateString = function (str) {
		throw "updateString(str) not supported for this alg:prov=" + this.algProvName;
	};

	/**
	 * Updates the data to be signed or verified by a hexadecimal string
	 * @name updateHex
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {String} hex hexadecimal string to use for the update
	 * @description
	 * @example
	 * sig.updateHex('1f2f3f')
	 */
	this.updateHex = function (hex) {
		throw "updateHex(hex) not supported for this alg:prov=" + this.algProvName;
	};

	/**
	 * Returns the signature bytes of all data updates as a hexadecimal string
	 * @name sign
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @return the signature bytes as a hexadecimal string
	 * @description
	 * @example
	 * var hSigValue = sig.sign()
	 */
	this.sign = function () {
		throw "sign() not supported for this alg:prov=" + this.algProvName;
	};

	/**
	 * performs final update on the sign using string, then returns the signature bytes of all data updates as a hexadecimal string
	 * @name signString
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {String} str string to final update
	 * @return the signature bytes of a hexadecimal string
	 * @description
	 * @example
	 * var hSigValue = sig.signString('aaa')
	 */
	this.signString = function (str) {
		throw "digestString(str) not supported for this alg:prov=" + this.algProvName;
	};

	/**
	 * performs final update on the sign using hexadecimal string, then returns the signature bytes of all data updates as a hexadecimal string
	 * @name signHex
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {String} hex hexadecimal string to final update
	 * @return the signature bytes of a hexadecimal string
	 * @description
	 * @example
	 * var hSigValue = sig.signHex('1fdc33')
	 */
	this.signHex = function (hex) {
		throw "digestHex(hex) not supported for this alg:prov=" + this.algProvName;
	};

	/**
	 * verifies the passed-in signature.
	 * @name verify
	 * @memberOf KJUR.crypto.Signature#
	 * @function
	 * @param {String} str string to final update
	 * @return {Boolean} true if the signature was verified, otherwise false
	 * @description
	 * @example
	 * var isValid = sig.verify('1fbcefdca4823a7(snip)')
	 */
	this.verify = function (hSigVal) {
		throw "verify(hSigVal) not supported for this alg:prov=" + this.algProvName;
	};

	this.initParams = params;

	if (params !== undefined) {
		if (params.alg !== undefined) {
			this.algName = params.alg;
			if (params.prov === undefined) {
				this.provName = KJUR.crypto.Util.DEFAULTPROVIDER[this.algName];
			} else {
				this.provName = params.prov;
			}
			this.algProvName = this.algName + ":" + this.provName;
			this.setAlgAndProvider(this.algName, this.provName);
			this._setAlgNames();
		}

		if (params['psssaltlen'] !== undefined) this.pssSaltLen = params['psssaltlen'];

		if (params.prvkeypem !== undefined) {
			if (params.prvkeypas !== undefined) {
				throw "both prvkeypem and prvkeypas parameters not supported";
			} else {
				try {
					var prvKey = KEYUTIL.getKey(params.prvkeypem);
					this.init(prvKey);
				} catch (ex) {
					throw "fatal error to load pem private key: " + ex;
				}
			}
		}
	}
};

// ====== Cipher class ============================================================
/**
 * Cipher class to encrypt and decrypt data<br/>
 * @name KJUR.crypto.Cipher
 * @class Cipher class to encrypt and decrypt data<br/>
 * @param {Array} params parameters for constructor
 * @since jsrsasign 6.2.0 crypto 1.1.10
 * @description
 * Here is supported canonicalized cipher algorithm names and its standard names:
 * <ul>
 * <li>RSA - RSA/ECB/PKCS1Padding (default for RSAKey)</li>
 * <li>RSAOAEP - RSA/ECB/OAEPWithSHA-1AndMGF1Padding</li>
 * <li>RSAOAEP224 - RSA/ECB/OAEPWithSHA-224AndMGF1Padding(*)</li>
 * <li>RSAOAEP256 - RSA/ECB/OAEPWithSHA-256AndMGF1Padding</li>
 * <li>RSAOAEP384 - RSA/ECB/OAEPWithSHA-384AndMGF1Padding(*)</li>
 * <li>RSAOAEP512 - RSA/ECB/OAEPWithSHA-512AndMGF1Padding(*)</li>
 * </ul>
 * NOTE: (*) is not supported in Java JCE.<br/>
 * Currently this class supports only RSA encryption and decryption 
 * based on RSAES-OAEP and RSAES-PKCS1-v1_5 scheme. 
 * However it is planning to implement also symmetric ciphers near in the future */
KJUR.crypto.Cipher = function (params) {
};

/**
 * encrypt raw string by specified key and algorithm<br/>
 * @name encrypt
 * @memberOf KJUR.crypto.Cipher
 * @function
 * @param {String} s input string to encrypt
 * @param {Object} keyObj RSAKey object or hexadecimal string of symmetric cipher key
 * @param {String} algName short/long algorithm name for encryption/decryption 
 * @return {String} hexadecimal encrypted string
 * @since jsrsasign 6.2.0 crypto 1.1.10
 * @description
 * This static method encrypts raw string with specified key and algorithm.
 * @example 
 * KJUR.crypto.Cipher.encrypt("aaa", pubRSAKeyObj) &rarr; "1abc2d..."
 * KJUR.crypto.Cipher.encrypt("aaa", pubRSAKeyObj, "RSAOAEP") &rarr; "23ab02..."
 */
KJUR.crypto.Cipher.encrypt = function (s, keyObj, algName) {
	if (keyObj instanceof RSAKey && keyObj.isPublic) {
		var algName2 = KJUR.crypto.Cipher.getAlgByKeyAndName(keyObj, algName);
		if (algName2 === "RSA") return keyObj.encrypt(s);
		if (algName2 === "RSAOAEP") return keyObj.encryptOAEP(s, "sha1");

		var a = algName2.match(/^RSAOAEP(\d+)$/);
		if (a !== null) return keyObj.encryptOAEP(s, "sha" + a[1]);

		throw "Cipher.encrypt: unsupported algorithm for RSAKey: " + algName;
	} else {
		throw "Cipher.encrypt: unsupported key or algorithm";
	}
};

/**
 * decrypt encrypted hexadecimal string with specified key and algorithm<br/>
 * @name decrypt
 * @memberOf KJUR.crypto.Cipher
 * @function
 * @param {String} hex hexadecial string of encrypted message
 * @param {Object} keyObj RSAKey object or hexadecimal string of symmetric cipher key
 * @param {String} algName short/long algorithm name for encryption/decryption
 * @return {String} decrypted raw string
 * @since jsrsasign 6.2.0 crypto 1.1.10
 * @description
 * This static method decrypts encrypted hexadecimal string with specified key and algorithm.
 * @example 
 * KJUR.crypto.Cipher.decrypt("aaa", prvRSAKeyObj) &rarr; "1abc2d..."
 * KJUR.crypto.Cipher.decrypt("aaa", prvRSAKeyObj, "RSAOAEP) &rarr; "23ab02..."
 */
KJUR.crypto.Cipher.decrypt = function (hex, keyObj, algName) {
	if (keyObj instanceof RSAKey && keyObj.isPrivate) {
		var algName2 = KJUR.crypto.Cipher.getAlgByKeyAndName(keyObj, algName);
		if (algName2 === "RSA") return keyObj.decrypt(hex);
		if (algName2 === "RSAOAEP") return keyObj.decryptOAEP(hex, "sha1");

		var a = algName2.match(/^RSAOAEP(\d+)$/);
		if (a !== null) return keyObj.decryptOAEP(hex, "sha" + a[1]);

		throw "Cipher.decrypt: unsupported algorithm for RSAKey: " + algName;
	} else {
		throw "Cipher.decrypt: unsupported key or algorithm";
	}
};

/**
 * get canonicalized encrypt/decrypt algorithm name by key and short/long algorithm name<br/>
 * @name getAlgByKeyAndName
 * @memberOf KJUR.crypto.Cipher
 * @function
 * @param {Object} keyObj RSAKey object or hexadecimal string of symmetric cipher key
 * @param {String} algName short/long algorithm name for encryption/decryption
 * @return {String} canonicalized algorithm name for encryption/decryption
 * @since jsrsasign 6.2.0 crypto 1.1.10
 * @description
 * Here is supported canonicalized cipher algorithm names and its standard names:
 * <ul>
 * <li>RSA - RSA/ECB/PKCS1Padding (default for RSAKey)</li>
 * <li>RSAOAEP - RSA/ECB/OAEPWithSHA-1AndMGF1Padding</li>
 * <li>RSAOAEP224 - RSA/ECB/OAEPWithSHA-224AndMGF1Padding(*)</li>
 * <li>RSAOAEP256 - RSA/ECB/OAEPWithSHA-256AndMGF1Padding</li>
 * <li>RSAOAEP384 - RSA/ECB/OAEPWithSHA-384AndMGF1Padding(*)</li>
 * <li>RSAOAEP512 - RSA/ECB/OAEPWithSHA-512AndMGF1Padding(*)</li>
 * </ul>
 * NOTE: (*) is not supported in Java JCE.
 * @example 
 * KJUR.crypto.Cipher.getAlgByKeyAndName(objRSAKey) &rarr; "RSA"
 * KJUR.crypto.Cipher.getAlgByKeyAndName(objRSAKey, "RSAOAEP") &rarr; "RSAOAEP"
 */
KJUR.crypto.Cipher.getAlgByKeyAndName = function (keyObj, algName) {
	if (keyObj instanceof RSAKey) {
		if (":RSA:RSAOAEP:RSAOAEP224:RSAOAEP256:RSAOAEP384:RSAOAEP512:".indexOf(algName) != -1)
			return algName;
		if (algName === null || algName === undefined) return "RSA";
		throw "getAlgByKeyAndName: not supported algorithm name for RSAKey: " + algName;
	}
	throw "getAlgByKeyAndName: not supported algorithm name: " + algName;
}

// ====== Other Utility class =====================================================

/**
 * static object for cryptographic function utilities
 * @name KJUR.crypto.OID
 * @class static object for cryptography related OIDs
 * @property {Array} oidhex2name key value of hexadecimal OID and its name
 *           (ex. '2a8648ce3d030107' and 'secp256r1')
 * @since crypto 1.1.3
 * @description
 */
KJUR.crypto.OID = new function () {
	this.oidhex2name = {
		'2a864886f70d010101': 'rsaEncryption',
		'2a8648ce3d0201': 'ecPublicKey',
		'2a8648ce380401': 'dsa',
		'2a8648ce3d030107': 'secp256r1',
		'2b8104001f': 'secp192k1',
		'2b81040021': 'secp224r1',
		'2b8104000a': 'secp256k1',
		'2b81040023': 'secp521r1',
		'2b81040022': 'secp384r1',
		'2a8648ce380403': 'SHA1withDSA', // 1.2.840.10040.4.3
		'608648016503040301': 'SHA224withDSA', // 2.16.840.1.101.3.4.3.1
		'608648016503040302': 'SHA256withDSA', // 2.16.840.1.101.3.4.3.2
	};
};

/* device types */
var MultiVerBoard = {
	"WS7100-10": {
		"productTitle": "华为路由AX3",
		"product_title_index": '华为路由AX3',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">华为路由AX3</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">华为路由AX3</span>',
		"productName": "WS7100-10",
		"logoClass": "ic-huaweilogo",
		"leadLogoClass": "ic_lead_huaweilogo",
		"contentDeviceClass": "ic_content_status_huawei",
		"qrcodeRenew": "qrcode_huawei",
		"icRouterHiClass": "ic_router_hi_huawei",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_pro_upgrade",
		"icHttpstatusfailedClass": "ic_pro_httpstatusfailed",
		"icUncableClass": "ic_uncable_pro",
		"icGuideLearningClass": "learn_pro",
		"icGuide2LearningClass": "ic_learn_pro",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard_7200-10",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_huawei",
		"Touchui_GuideRenewClass": "router_renew_826",
		"Touchui_GuideLearningClass": "learning_Pro",
		"Touchui_Guide2LearningClass": "learning_2_Pro",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard01",
		"Touchui_GuideUncabledClass": "uncablefailed_Pro",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_Pro",
		"icShowdoublewanClass": "show_doublewan01",
		"icShowsinglewanClass": "show_singlewan01",
		"Forum": "http://cn.club.vmall.com/"
	},
	"WS7103-10": {
		"productTitle": "华为路由WS7103",
		"product_title_index": '华为路由WS7103',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">华为路由WS7103</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">华为路由WS7103</span>',
		"productName": "WS7103-10",
		"logoClass": "ic-huaweilogo",
		"leadLogoClass": "ic_lead_huaweilogo",
		"contentDeviceClass": "ic_content_status_huawei",
		"qrcodeRenew": "qrcode_huawei",
		"icRouterHiClass": "ic_router_hi_huawei",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_pro_upgrade",
		"icHttpstatusfailedClass": "ic_pro_httpstatusfailed",
		"icUncableClass": "ic_uncable_pro",
		"icGuideLearningClass": "learn_pro",
		"icGuide2LearningClass": "ic_learn_pro",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard_7200-10",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_huawei",
		"Touchui_GuideRenewClass": "router_renew_826",
		"Touchui_GuideLearningClass": "learning_Pro",
		"Touchui_Guide2LearningClass": "learning_2_Pro",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard01",
		"Touchui_GuideUncabledClass": "uncablefailed_Pro",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_Pro",
		"icShowdoublewanClass": "show_doublewan01",
		"icShowsinglewanClass": "show_singlewan01",
		"Forum": "http://cn.club.vmall.com/"
	},
	"TC7102-10": {
		"productTitle": "华为路由TC7102",
		"product_title_index": '华为路由TC7102',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">华为路由TC7102</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">华为路由TC7102</span>',
		"productName": "TC7102-10",
		"logoClass": "ic-huaweilogo",
		"leadLogoClass": "ic_lead_huaweilogo",
		"contentDeviceClass": "ic_content_status_huawei",
		"qrcodeRenew": "qrcode_huawei",
		"icRouterHiClass": "ic_router_hi_huawei",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_pro_upgrade",
		"icHttpstatusfailedClass": "ic_pro_httpstatusfailed",
		"icUncableClass": "ic_uncable_pro",
		"icGuideLearningClass": "learn_pro",
		"icGuide2LearningClass": "ic_learn_pro",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard_7200-10",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_huawei",
		"Touchui_GuideRenewClass": "router_renew_826",
		"Touchui_GuideLearningClass": "learning_Pro",
		"Touchui_Guide2LearningClass": "learning_2_Pro",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard01",
		"Touchui_GuideUncabledClass": "uncablefailed_Pro",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_Pro",
		"icShowdoublewanClass": "show_doublewan01",
		"icShowsinglewanClass": "show_singlewan01",
		"Forum": "http://cn.club.vmall.com/"
	},
	"XD20-10": {
		"productTitle": "荣耀路由3",
		"product_title_index": '荣耀路由3',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">荣耀路由3</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">荣耀路由3</span>',
		"productName": "XD20-10",
		"logoClass": "ic-honorlogo",
		"leadLogoClass": "ic_lead_honorlogo",
		"contentDeviceClass": "ic_content_status_honor",
		"qrcodeRenew": "qrcode_honor",
		"icRouterHiClass": "ic_router_hi_honor",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_router_upgrade",
		"icHttpstatusfailedClass": "ic_s1_httpstatusfailed",
		"icUncableClass": "ic_uncable_s1",
		"icGuideLearningClass": "learn_pro2",
		"icGuide2LearningClass": "ic_learn_pro2",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard02",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_honor",
		"Touchui_GuideRenewClass": "router_renew_S1",
		"Touchui_GuideLearningClass": "learning_S1",
		"Touchui_Guide2LearningClass": "learning_2_S1",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard02",
		"Touchui_GuideUncabledClass": "uncablefailed_S1",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_S1",
		"icShowdoublewanClass": "show_doublewan03",
		"icShowsinglewanClass": "show_singlewan03",
		"Forum": "http://cn.club.vmall.com/"
	},
	"XD22-10": {
		"productTitle": "荣耀路由XD22",
		"product_title_index": '荣耀路由XD22',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">荣耀路由XD22</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">荣耀路由XD22</span>',
		"productName": "XD22-10",
		"logoClass": "ic-honorlogo",
		"leadLogoClass": "ic_lead_honorlogo",
		"contentDeviceClass": "ic_content_status_honor",
		"qrcodeRenew": "qrcode_honor",
		"icRouterHiClass": "ic_router_hi_honor",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_router_upgrade",
		"icHttpstatusfailedClass": "ic_s1_httpstatusfailed",
		"icUncableClass": "ic_uncable_s1",
		"icGuideLearningClass": "learn_pro2",
		"icGuide2LearningClass": "ic_learn_pro2",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard02",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_honor",
		"Touchui_GuideRenewClass": "router_renew_S1",
		"Touchui_GuideLearningClass": "learning_S1",
		"Touchui_Guide2LearningClass": "learning_2_S1",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard02",
		"Touchui_GuideUncabledClass": "uncablefailed_S1",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_S1",
		"icShowdoublewanClass": "show_doublewan03",
		"icShowsinglewanClass": "show_singlewan03",
		"Forum": "http://cn.club.vmall.com/"
	},
	"XD21-10": {
		"productTitle": "荣耀路由XD21",
		"product_title_index": '荣耀路由XD21',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">荣耀路由XD21</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">荣耀路由XD21</span>',
		"productName": "XD21-10",
		"logoClass": "ic-honorlogo",
		"leadLogoClass": "ic_lead_honorlogo",
		"contentDeviceClass": "ic_content_status_honor",
		"qrcodeRenew": "qrcode_honor",
		"icRouterHiClass": "ic_router_hi_honor",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_router_upgrade",
		"icHttpstatusfailedClass": "ic_s1_httpstatusfailed",
		"icUncableClass": "ic_uncable_s1",
		"icGuideLearningClass": "learn_pro2",
		"icGuide2LearningClass": "ic_learn_pro2",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard02",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_honor",
		"Touchui_GuideRenewClass": "router_renew_S1",
		"Touchui_GuideLearningClass": "learning_S1",
		"Touchui_Guide2LearningClass": "learning_2_S1",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard02",
		"Touchui_GuideUncabledClass": "uncablefailed_S1",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_S1",
		"icShowdoublewanClass": "show_doublewan03",
		"icShowsinglewanClass": "show_singlewan03",
		"Forum": "http://cn.club.vmall.com/"
	},
	"XD23-10": {
		"productTitle": "荣耀路由XD23",
		"product_title_index": '荣耀路由XD23',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">荣耀路由XD23</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">荣耀路由XD23</span>',
		"productName": "XD23-10",
		"logoClass": "ic-honorlogo",
		"leadLogoClass": "ic_lead_honorlogo",
		"contentDeviceClass": "ic_content_status_honor",
		"qrcodeRenew": "qrcode_honor",
		"icRouterHiClass": "ic_router_hi_honor",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_router_upgrade",
		"icHttpstatusfailedClass": "ic_s1_httpstatusfailed",
		"icUncableClass": "ic_uncable_s1",
		"icGuideLearningClass": "learn_pro2",
		"icGuide2LearningClass": "ic_learn_pro2",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard02",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_honor",
		"Touchui_GuideRenewClass": "router_renew_S1",
		"Touchui_GuideLearningClass": "learning_S1",
		"Touchui_Guide2LearningClass": "learning_2_S1",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard02",
		"Touchui_GuideUncabledClass": "uncablefailed_S1",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_S1",
		"icShowdoublewanClass": "show_doublewan03",
		"icShowsinglewanClass": "show_singlewan03",
		"Forum": "http://cn.club.vmall.com/"
	},
	"XD24-10": {
		"productTitle": "荣耀路由3 Z6",
		"product_title_index": '荣耀路由3 Z6',
		"product_title_guide": '欢迎使用<span style="font-size:26px;">荣耀路由3 Z6</span>',
		"product_title_guide_touchui": '欢迎使用<span style="font-size:30px;">荣耀路由3 Z6</span>',
		"productName": "XD24-10",
		"logoClass": "ic-honorlogo",
		"leadLogoClass": "ic_lead_honorlogo",
		"contentDeviceClass": "ic_content_status_honor",
		"qrcodeRenew": "qrcode_honor",
		"icRouterHiClass": "ic_router_hi_honor",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_router_upgrade",
		"icHttpstatusfailedClass": "ic_s1_httpstatusfailed",
		"icUncableClass": "ic_uncable_s1",
		"icGuideLearningClass": "learn_pro2",
		"icGuide2LearningClass": "ic_learn_pro2",
		"Learnoldethdownsecond": "learn_success_ethup_multiboard02",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_honor",
		"Touchui_GuideRenewClass": "router_renew_S1",
		"Touchui_GuideLearningClass": "learning_S1",
		"Touchui_Guide2LearningClass": "learning_2_S1",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup_multiboard02",
		"Touchui_GuideUncabledClass": "uncablefailed_S1",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_S1",
		"icShowdoublewanClass": "show_doublewan03",
		"icShowsinglewanClass": "show_singlewan03",
		"Forum": "http://cn.club.vmall.com/"
	},
	"default": {
		"productTitle": "华为路由AX3",
		"product_title_index": "华为路由AX3",
		"product_title_guide": "欢迎使用华为路由AX3",
		"product_title_guide_touchui": "欢迎使用华为路由AX3",
		"productName": "华为路由AX3",
		"logoClass": "ic-logo",
		"leadLogoClass": "ic_lead_honorlogo",
		"contentDeviceClass": "ic_content_router",
		"qrcodeRenew": "qrcode_ic",
		"icRouterHiClass": "ic_router_hi",
		"icTopoSelfClass": "ic_router_huawei",
		"icUpgradeSelfClass": "ic_router_upgrade",
		"icHttpstatusfailedClass": "ic_router_httpstatusfailed",
		"icUncableClass": "ic_uncable_router",
		"icGuideLearningClass": "learn_router",
		"icGuide2LearningClass": "ic_learn_router",
		"Learnoldethdownsecond": "learn_success_ethup",
		"Touchui_GuideWelcomeClass": "welcomeliving_shape_status_imgs_huawei",
		"Touchui_GuideRenewClass": "router_renew_emui",
		"Touchui_GuideLearningClass": "learning_emui",
		"Touchui_Guide2LearningClass": "learning_2_emui",
		"Touchui_GuideLearnoldethClass": "learn_success_ethup",
		"Touchui_GuideUncabledClass": "uncablefailed_emui",
		"Touchui_GuideHttpstatusfailedClass": "httpstatusfailed_emui",
		"icShowdoublewanClass": "show_doublewan",
		"icShowsinglewanClass": "show_singlewan",
		"Forum": "http://cn.club.vmall.com/"
	}
}
/* device types end */

