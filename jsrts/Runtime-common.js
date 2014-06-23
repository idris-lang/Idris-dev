/** @constructor */
var i$VM = function() {
  this.valstack = [];
  this.valstack_top = 0;
  this.valstack_base = 0;

  this.ret = null;
  this.reg1 = null;

  this.callstack = [];
}

/** @constructor */
var i$CON = function(tag,args,app,ev) {
  this.tag = tag;
  this.args = args;
  this.app = app;
  this.ev = ev;
}

var i$SLIDE = function(vm,args) {
  for (var i = 0; i < args; ++i)
    vm.valstack[vm.valstack_base + i] = vm.valstack[vm.valstack_top + i];
}

var i$PROJECT = function(vm,val,loc,arity) {
  for (var i = 0; i < arity; ++i)
    vm.valstack[vm.valstack_base + i + loc] = val.args[i];
}

var i$CALL = function(vm,fun,args) {
  vm.callstack.push(args);
  vm.callstack.push(fun);
}

var __IDRRT__charCode = function(str) {
  if (typeof str == "string")
    return str.charCodeAt(0);
  else
    return str;
}

var __IDRRT__fromCharCode = function(chr) {
  if (typeof chr == "string")
    return chr;
  else
    return String.fromCharCode(chr);
}

var isNull = function(v) {
  return v == null;
}
