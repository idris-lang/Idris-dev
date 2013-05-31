var __IDRRT__ = {};

/** @constructor */
__IDRRT__.Type = function(type) {
  this.type = type;
};

__IDRRT__.Int = new __IDRRT__.Type('Int');
__IDRRT__.Char = new __IDRRT__.Type('Char');
__IDRRT__.String = new __IDRRT__.Type('String');
__IDRRT__.Integer = new __IDRRT__.Type('Integer');
__IDRRT__.Float = new __IDRRT__.Type('Float');
__IDRRT__.Ptr = new __IDRRT__.Type('Pointer');
__IDRRT__.Forgot = new __IDRRT__.Type('Forgot');


/** @constructor */
__IDRRT__.Tailcall = function(f) { this.f = f };
__IDRRT__.ffiWrap = function(fid) {
  return function(arg) {
    return __IDRRT__.tailcall(function(){
      return __IDR__.APPLY0(fid, arg);
    });
  };
};

/** @constructor */
__IDRRT__.Con = function(i,vars) {
  this.i = i;
  this.vars =  vars;
};

__IDRRT__.tailcall = function(f) {
  var __f = f;
  var ret;
  while (__f) {
    f = __f;
    __f = null;
    ret = f();

    if (ret instanceof __IDRRT__.Tailcall) {
      __f = ret.f;
    } else {
      return ret;
    }
  }
};

/*
   BigInteger Javascript code taken from:
   https://github.com/peterolson
*/
__IDRRT__.bigInt = (function () {
  var base = 10000000, logBase = 7;
  var sign = {
    positive: false,
  negative: true
  };

  var normalize = function (first, second) {
    var a = first.value, b = second.value;
    var length = a.length > b.length ? a.length : b.length;
    for (var i = 0; i < length; i++) {
      a[i] = a[i] || 0;
      b[i] = b[i] || 0;
    }
    for (var i = length - 1; i >= 0; i--) {
      if (a[i] === 0 && b[i] === 0) {
        a.pop();
        b.pop();
      } else break;
    }
    if (!a.length) a = [0], b = [0];
    first.value = a;
    second.value = b;
  };

  var parse = function (text, first) {
    if (typeof text === "object") return text;
    text += "";
    var s = sign.positive, value = [];
    if (text[0] === "-") {
      s = sign.negative;
      text = text.slice(1);
    }
    var text = text.split("e");
    if (text.length > 2) throw new Error("Invalid integer");
    if (text[1]) {
      var exp = text[1];
      if (exp[0] === "+") exp = exp.slice(1);
      exp = parse(exp);
      if (exp.lesser(0)) throw new Error("Cannot include negative exponent part for integers");
      while (exp.notEquals(0)) {
        text[0] += "0";
        exp = exp.prev();
      }
    }
    text = text[0];
    if (text === "-0") text = "0";
    var isValid = /^([0-9][0-9]*)$/.test(text);
    if (!isValid) throw new Error("Invalid integer");
    while (text.length) {
      var divider = text.length > logBase ? text.length - logBase : 0;
      value.push(+text.slice(divider));
      text = text.slice(0, divider);
    }
    var val = bigInt(value, s);
    if (first) normalize(first, val);
    return val;
  };

  var goesInto = function (a, b) {
    var a = bigInt(a, sign.positive), b = bigInt(b, sign.positive);
    if (a.equals(0)) throw new Error("Cannot divide by 0");
    var n = 0;
    do {
      var inc = 1;
      var c = bigInt(a.value, sign.positive), t = c.times(10);
      while (t.lesser(b)) {
        c = t;
        inc *= 10;
        t = t.times(10);
      }
      while (c.lesserOrEquals(b)) {
        b = b.minus(c);
        n += inc;
      }
    } while (a.lesserOrEquals(b));

    return {
      remainder: b.value,
        result: n
    };
  };

  var bigInt = function (value, s) {
    var self = {
      value: value,
      sign: s
    };
    var o = {
      value: value,
      sign: s,
      negate: function (m) {
        var first = m || self;
        return bigInt(first.value, !first.sign);
      },
      abs: function (m) {
        var first = m || self;
        return bigInt(first.value, sign.positive);
      },
      add: function (n, m) {
        var s, first = self, second;
        if (m) (first = parse(n)) && (second = parse(m));
        else second = parse(n, first);
        s = first.sign;
        if (first.sign !== second.sign) {
          first = bigInt(first.value, sign.positive);
          second = bigInt(second.value, sign.positive);
          return s === sign.positive ?
            o.subtract(first, second) :
            o.subtract(second, first);
        }
        normalize(first, second);
        var a = first.value, b = second.value;
        var result = [],
            carry = 0;
        for (var i = 0; i < a.length || carry > 0; i++) {
          var sum = (a[i] || 0) + (b[i] || 0) + carry;
          carry = sum >= base ? 1 : 0;
          sum -= carry * base;
          result.push(sum);
        }
        return bigInt(result, s);
      },
      plus: function (n, m) {
        return o.add(n, m);
      },
      subtract: function (n, m) {
        var first = self, second;
        if (m) (first = parse(n)) && (second = parse(m));
        else second = parse(n, first);
        if (first.sign !== second.sign) return o.add(first, o.negate(second));
        if (first.sign === sign.negative) return o.subtract(o.negate(second), o.negate(first));
        if (o.compare(first, second) === -1) return o.negate(o.subtract(second, first));
        var a = first.value, b = second.value;
        var result = [],
            borrow = 0;
        for (var i = 0; i < a.length; i++) {
          a[i] -= borrow;
          borrow = a[i] < b[i] ? 1 : 0;
          var minuend = (borrow * base) + a[i] - b[i];
          result.push(minuend);
        }
        return bigInt(result, sign.positive);
      },
      minus: function (n, m) {
        return o.subtract(n, m);
      },
      multiply: function (n, m) {
        var s, first = self, second;
        if (m) (first = parse(n)) && (second = parse(m));
        else second = parse(n, first);
        s = first.sign !== second.sign;
        var a = first.value, b = second.value;
        var resultSum = [];
        for (var i = 0; i < a.length; i++) {
          resultSum[i] = [];
          var j = i;
          while (j--) {
            resultSum[i].push(0);
          }
        }
        var carry = 0;
        for (var i = 0; i < a.length; i++) {
          var x = a[i];
          for (var j = 0; j < b.length || carry > 0; j++) {
            var y = b[j];
            var product = y ? (x * y) + carry : carry;
            carry = product > base ? Math.floor(product / base) : 0;
            product -= carry * base;
            resultSum[i].push(product);
          }
        }
        var max = -1;
        for (var i = 0; i < resultSum.length; i++) {
          var len = resultSum[i].length;
          if (len > max) max = len;
        }
        var result = [], carry = 0;
        for (var i = 0; i < max || carry > 0; i++) {
          var sum = carry;
          for (var j = 0; j < resultSum.length; j++) {
            sum += resultSum[j][i] || 0;
          }
          carry = sum > base ? Math.floor(sum / base) : 0;
          sum -= carry * base;
          result.push(sum);
        }
        return bigInt(result, s);
      },
      times: function (n, m) {
        return o.multiply(n, m);
      },
      divmod: function (n, m) {
        var s, first = self, second;
        if (m) (first = parse(n)) && (second = parse(m));
        else second = parse(n, first);
        s = first.sign !== second.sign;
        if (bigInt(first.value, first.sign).equals(0)) return {
          quotient: bigInt([0], sign.positive),
            remainder: bigInt([0], sign.positive)
        };
        if (second.equals(0)) throw new Error("Cannot divide by zero");
        var a = first.value, b = second.value;
        var result = [], remainder = [];
        for (var i = a.length - 1; i >= 0; i--) {
          var n = [a[i]].concat(remainder);
          var quotient = goesInto(b, n);
          result.push(quotient.result);
          remainder = quotient.remainder;
        }
        result.reverse();
        return {
          quotient: bigInt(result, s),
            remainder: bigInt(remainder, first.sign)
        };
      },
      divide: function (n, m) {
        return o.divmod(n, m).quotient;
      },
      over: function (n, m) {
        return o.divide(n, m);
      },
      mod: function (n, m) {
        return o.divmod(n, m).remainder;
      },
      pow: function (n, m) {
        var first = self, second;
        if (m) (first = parse(n)) && (second = parse(m));
        else second = parse(n, first);
        var a = first, b = second;
        if (b.lesser(0)) return ZERO;
        if (b.equals(0)) return ONE;
        var result = bigInt(a.value, a.sign);

        if (b.mod(2).equals(0)) {
          var c = result.pow(b.over(2));
          return c.times(c);
        } else {
          return result.times(result.pow(b.minus(1)));
        }
      },
      next: function (m) {
        var first = m || self;
        return o.add(first, 1);
      },
      prev: function (m) {
        var first = m || self;
        return o.subtract(first, 1);
      },
      compare: function (n, m) {
        var first = self, second;
        if (m) (first = parse(n)) && (second = parse(m, first));
        else second = parse(n, first);
        normalize(first, second);
        if (first.value.length === 1 && second.value.length === 1 && first.value[0] === 0 && second.value[0] === 0) return 0;
        if (second.sign !== first.sign) return first.sign === sign.positive ? 1 : -1;
        var multiplier = first.sign === sign.positive ? 1 : -1;
        var a = first.value, b = second.value;
        for (var i = a.length - 1; i >= 0; i--) {
          if (a[i] > b[i]) return 1 * multiplier;
          if (b[i] > a[i]) return -1 * multiplier;
        }
        return 0;
      },
      compareAbs: function (n, m) {
        var first = self, second;
        if (m) (first = parse(n)) && (second = parse(m, first));
        else second = parse(n, first);
        first.sign = second.sign = sign.positive;
        return o.compare(first, second);
      },
      equals: function (n, m) {
        return o.compare(n, m) === 0;
      },
      notEquals: function (n, m) {
        return !o.equals(n, m);
      },
      lesser: function (n, m) {
        return o.compare(n, m) < 0;
      },
      greater: function (n, m) {
        return o.compare(n, m) > 0;
      },
      greaterOrEquals: function (n, m) {
        return o.compare(n, m) >= 0;
      },
      lesserOrEquals: function (n, m) {
        return o.compare(n, m) <= 0;
      },
      isPositive: function (m) {
        var first = m || self;
        return first.sign === sign.positive;
      },
      isNegative: function (m) {
        var first = m || self;
        return first.sign === sign.negative;
      },
      isEven: function (m) {
        var first = m || self;
        return first.value[0] % 2 === 0;
      },
      isOdd: function (m) {
        var first = m || self;
        return first.value[0] % 2 === 1;
      },
      toString: function (m) {
        var first = m || self;
        var str = "", len = first.value.length;
        while (len--) {
          str += (base.toString() + first.value[len]).slice(-logBase);
        }
        while (str[0] === "0") {
          str = str.slice(1);
        }
        if (!str.length) str = "0";
        var s = first.sign === sign.positive ? "" : "-";
        return s + str;
      },
      toJSNumber: function (m) {
        return +o.toString(m);
      },
      valueOf: function (m) {
        return o.toJSNumber(m);
      }
    };
    return o;
  };

  var ZERO = bigInt([0], sign.positive);
  var ONE = bigInt([1], sign.positive);
  var MINUS_ONE = bigInt([1], sign.negative);

  var fnReturn = function (a) {
    if (typeof a === "undefined") return ZERO;
    return parse(a);
  };
  fnReturn.zero = ZERO;
  fnReturn.one = ONE;
  fnReturn.minusOne = MINUS_ONE;
  return fnReturn;
})();

var __IDR__ = {};
