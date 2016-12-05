/** @constructor */
var i$VM = function() {
  this.valstack = {};
  this.valstack_top = 0;
  this.valstack_base = 0;

  this.ret = null;

  this.callstack = [];
}

var i$vm;
var i$valstack;
var i$valstack_top;
var i$valstack_base;
var i$ret;
var i$callstack;

var i$Int = {};
var i$String = {};
var i$Integer = {};
var i$Float = {};
var i$Char = {};
var i$Ptr = {};
var i$Forgot = {};

/** @constructor */
var i$CON = function(tag,args,app,ev) {
  this.tag = tag;
  this.args = args;
  this.app = app;
  this.ev = ev;
}

/** @constructor */
var i$POINTER = function(addr) {
  this.addr = addr;
}

var i$SCHED = function(vm) {
  i$vm = vm;
  i$valstack = vm.valstack;
  i$valstack_top = vm.valstack_top;
  i$valstack_base = vm.valstack_base;
  i$ret = vm.ret;
  i$callstack = vm.callstack;
}

var i$SLIDE = function(args) {
  for (var i = 0; i < args; ++i)
    i$valstack[i$valstack_base + i] = i$valstack[i$valstack_top + i];
}

var i$PROJECT = function(val,loc,arity) {
  for (var i = 0; i < arity; ++i)
    i$valstack[i$valstack_base + i + loc] = val.args[i];
}

var i$CALL = function(fun,args) {
  i$callstack.push(args);
  i$callstack.push(fun);
}

var i$ffiWrap = function(fid,oldbase,myoldbase) {
  return function() {
    var oldstack = i$callstack;
    i$callstack = [];

    var res = fid;

    for(var i = 0; i < (arguments.length ? arguments.length : 1); ++i) {
      while (res instanceof i$CON) {
        i$valstack_top += 1;
        i$valstack[i$valstack_top] = res;
        i$valstack[i$valstack_top + 1] = arguments[i];
        i$SLIDE(2);
        i$valstack_top = i$valstack_base + 2;
        i$CALL(_idris__123_APPLY0_125_,[oldbase])
        while (i$callstack.length) {
          var func = i$callstack.pop();
          var args = i$callstack.pop();
          func.apply(this,args);
        }
        res = i$ret;
      }
    }

    i$callstack = oldstack;

    return i$ret;
  }
}

var i$charCode = function(str) {
  if (typeof str == "string")
    return str.charCodeAt(0);
  else
    return str;
}

var i$fromCharCode = function(chr) {
  if (typeof chr == "string")
    return chr;
  else
    return String.fromCharCode(chr);
}

var i$RUN = function () {
  for (var i = 0; i < 10000 && i$callstack.length; i++) {
    var func = i$callstack.pop();
    var args = i$callstack.pop();
    func.apply(this,args);
  };

  if (i$callstack.length)
    setTimeout(i$RUN, 0);
}
