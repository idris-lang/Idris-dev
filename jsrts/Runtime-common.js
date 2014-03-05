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
