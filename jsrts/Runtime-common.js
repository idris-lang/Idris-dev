
var js_idris_throw2 = function (x){
 throw x;
}

var js_idris_force = function (x){
  if(x === undefined || x.js_idris_lazy_calc === undefined){
    return x
  }else{
    if(x.js_idris_lazy_val === undefined){
      x.js_idris_lazy_val = x.js_idris_lazy_calc()
    }
    return x.js_idris_lazy_val
  }
}
