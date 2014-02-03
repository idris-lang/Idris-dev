var __IDRRT__ZERO = __IDRRT__bigInt("0");
var __IDRRT__ONE = __IDRRT__bigInt("1");

/** @constructor */
var __IDRRT__Type = function(type) {
  this.type = type;
};

var __IDRRT__Int = new __IDRRT__Type('Int');
var __IDRRT__Char = new __IDRRT__Type('Char');
var __IDRRT__String = new __IDRRT__Type('String');
var __IDRRT__Integer = new __IDRRT__Type('Integer');
var __IDRRT__Float = new __IDRRT__Type('Float');
var __IDRRT__Ptr = new __IDRRT__Type('Pointer');
var __IDRRT__Forgot = new __IDRRT__Type('Forgot');

var __IDRRT__ffiWrap = function(fid) {
  return function(){
    var res = fid;
    var i = 0;
    var arg;
    while (res instanceof __IDRRT__Con){
      arg = arguments[i];
      res = __IDRRT__tailcall(function(){
        return __IDR__mAPPLY0(res, arg);
      });
      ++i;
    }
    return res;
  }
};

var __IDRRT__tailcall = function(k) {
  var ret = k();
  while (ret instanceof __IDRRT__Cont)
    ret = ret.k();

  return ret;
};

var __IDRRT__EVALTC = function(arg0) {
  var ret = (arg0 instanceof __IDRRT__Con && __IDRLT__mEVAL0[arg0.tag])?(__IDRLT__mEVAL0[arg0.tag](arg0)):(arg0);
  while (ret instanceof __IDRRT__Cont)
    ret = ret.k();

  return ret;
};

var __IDRRT__APPLYTC = function(fn0, arg0) {
  var ev  = __IDRRT__EVALTC(fn0);
  var ret = (ev instanceof __IDRRT__Con && __IDRLT__mAPPLY0[ev.tag])?(__IDRLT__mAPPLY0[ev.tag](fn0,arg0,ev)):(null)
  while (ret instanceof __IDRRT__Cont)
    ret = ret.k();

  return ret;
}
