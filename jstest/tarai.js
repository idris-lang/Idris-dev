#!/usr/bin/env node
"use strict";

(function(){

const jsbn = require('jsbn')
var fs = require('fs');
function $partial_5_6$u$io_95_bind(x1, x2, x3, x4, x5){
    return (function(x6){
        return u$io_95_bind(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_3_4$u$io_95_pure(x1, x2, x3){
    return (function(x4){
        return u$io_95_pure(x1, x2, x3, x4);
    });
}

function $partial_0_1$u$prim_95__95_toStrInt(){
    return (function(x1){
        return u$prim_95__95_toStrInt(x1);
    });
}

function $partial_2_3$u$prim_95_write(x1, x2){
    return (function(x3){
        return u$prim_95_write(x1, x2, x3);
    });
}

function $partial_0_1$q_2$Prelude$Show$t$primNumShow$0(){
    return (function(x1){
        return q_2$Prelude$Show$t$primNumShow$0(x1);
    });
}

function $partial_0_1$q_2$Prelude$Interactive$t$putStr_39_$0(){
    return (function(x1){
        return q_2$Prelude$Interactive$t$putStr_39_$0(x1);
    });
}

function $partial_6_7$t$io_95_bind$1(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return t$io_95_bind$1(x1, x2, x3, x4, x5, x6, x7);
    });
}


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

var js_idris_systemInfo = function(index) {
  var os = require('os')
    switch(index) {
      case 0:
        return "node";
      case 1:
        return os.platform();
    }
  return "";
}

function u$io_95_bind(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w){
    return t$io_95_bind$2(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w)(t$e$3(u$w));
}

function u$io_95_pure(t$e$0, t$e$1, t$e$2, u$w){
    return t$e$2;
}

function u$prim_95__95_toStrInt(t$op$0){
    return (''+(t$op$0));
}

function u$prim_95_write(t$e$0, t$e$1, u$w){
    return (process.stdout.write((t$e$1)));
}

function q_1$Main$u$main(){
    return q_2$Prelude$Interactive$u$putStr_39_(null, q_2$Prelude$Show$u$primNumShow(null, $partial_0_1$u$prim_95__95_toStrInt(), 0, q_1$Main$u$tarai(11, 5, 0)));
}

function q_2$Prelude$Show$u$precCon(t$e$0){
    
    if((t$e$0 === 0)) {
        return (new jsbn.BigInteger(("0")));
    } else {
        return (new jsbn.BigInteger(("5")));
    }
}

function q_2$Prelude$Show$u$primNumShow(t$e$0, t$e$1, t$e$2, t$e$3){
    const t$in$0 = t$e$1(t$e$3);
    let $cg$1 = null;
    if(q_2$Prelude$Interfaces$where$q_2$Prelude$Show$impl_1$q_2$Prelude$Interfaces$u$Ord$Prec$meth$u$_62__61_$0(t$e$2, 5)) {
        $cg$1 = q_2$Prelude$Show$t$primNumShow$2(t$in$0, t$e$0, t$e$1, t$e$2, t$e$3);
    } else {
        $cg$1 = false;
    }
    
    
    if($cg$1) {
        return ("(" + (t$in$0 + ")"));
    } else {
        return t$in$0;
    }
}

function q_2$Prelude$Interactive$u$putStr_39_(t$e$0, t$e$1){
    return $partial_5_6$u$io_95_bind(null, null, null, $partial_2_3$u$prim_95_write(null, t$e$1), $partial_0_1$q_2$Prelude$Interactive$t$putStr_39_$0());
}

function q_2$Prelude$Strings$u$strM(t$e$0){
    let $cg$1 = null;
    if((t$e$0 == "")) {
        $cg$1 = false;
    } else {
        $cg$1 = true;
    }
    
    
    if((q_2$Decidable$Equality$where$q_2$Decidable$Equality$impl_1$q_2$Decidable$Equality$u$DecEq$Bool$meth$u$decEq$0($cg$1, true) === 1)) {
        return 0;
    } else {
        return ({type: 1, $1: t$e$0[0]});
    }
}

function q_1$Main$u$tarai(t$e$0, t$e$1, t$e$2){
    let $tco$t$e$1 = t$e$1;
    let $tco$t$e$2 = t$e$2;
    for(;;) {
        
        if(q_2$Prelude$Interfaces$where$q_2$Prelude$Interfaces$impl_1$q_2$Prelude$Interfaces$u$Ord$Int$meth$u$_60__61_$0(t$e$0, t$e$1)) {
            return t$e$1;
        } else {
            $tco$t$e$1 = q_1$Main$u$tarai(((t$e$1)-(1)|0), t$e$2, t$e$0);
            $tco$t$e$2 = q_1$Main$u$tarai(((t$e$2)-(1)|0), t$e$0, t$e$1);
            t$e$0 = q_1$Main$u$tarai(((t$e$0)-(1)|0), t$e$1, t$e$2);
            t$e$1 = $tco$t$e$1;
            t$e$2 = $tco$t$e$2;
        }
    }
}

function q_2$Prelude$Interfaces$t$Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33__60__61__58_0_95_lam$0(t$e$0, t$e$1){
    return (t$e$0 === t$e$1);
}

function q_2$Prelude$Interfaces$t$Prelude__Show___64_Prelude__Interfaces__Ord_36_Prec_58__33__62__61__58_0_95_lam$0(t$e$0, t$e$1){
    return q_2$Prelude$Interfaces$where$q_2$Prelude$Show$impl_1$q_2$Prelude$Interfaces$u$Eq$Prec$meth$u$_61__61_$0(t$e$0, t$e$1);
}

function q_2$Prelude$Show$t$primNumShow$0(t$in$1){
    return (t$in$1 === "-");
}

function q_2$Prelude$Interactive$t$putStr_39_$0(t$in$0){
    return $partial_3_4$u$io_95_pure(null, null, 0);
}

function q_2$Prelude$Show$t$primNumShow$1(t$e$0, t$e$1, t$e$2, t$e$3, t$in$0, t$in$2){
    return $partial_0_1$q_2$Prelude$Show$t$primNumShow$0();
}

function q_2$Prelude$Show$t$primNumShow$2(t$in$0, t$e$0, t$e$1, t$e$2, t$e$3){
    const $cg$2 = q_2$Prelude$Strings$u$strM(t$in$0);
    if(($cg$2.type === 1)) {
        return q_2$Prelude$Show$t$primNumShow$1(t$e$0, t$e$1, t$e$2, t$e$3, t$in$0, $cg$2.$1)($cg$2.$1);
    } else {
        return false;
    }
}

function q_2$Decidable$Equality$where$q_2$Decidable$Equality$impl_1$q_2$Decidable$Equality$u$DecEq$Bool$meth$u$decEq$0(t$e$0, t$e$1){
    
    if(t$e$1) {
        
        if(t$e$0) {
            return 0;
        } else {
            return 1;
        }
    } else {
        
        if(t$e$0) {
            return 1;
        } else {
            return 0;
        }
    }
}

function q_2$Prelude$Interfaces$where$q_2$Prelude$Show$impl_1$q_2$Prelude$Interfaces$u$Eq$Prec$meth$u$_61__61_$0(t$e$0, t$e$1){
    
    return q_2$Prelude$Show$u$precCon(t$e$0).equals(q_2$Prelude$Show$u$precCon(t$e$1));
}

function q_2$Prelude$Interfaces$where$q_2$Prelude$Interfaces$impl_1$q_2$Prelude$Interfaces$u$Ord$Int$meth$u$_60__61_$0(t$e$0, t$e$1){
    let $cg$1 = null;
    if((q_2$Prelude$Interfaces$where$q_2$Prelude$Interfaces$impl_1$q_2$Prelude$Interfaces$u$Ord$Int$meth$u$compare$0(t$e$0, t$e$1) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    
    if($cg$1) {
        return true;
    } else {
        return q_2$Prelude$Interfaces$t$Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33__60__61__58_0_95_lam$0(t$e$0, t$e$1);
    }
}

function q_2$Prelude$Interfaces$where$q_2$Prelude$Interfaces$impl_1$q_2$Prelude$Interfaces$u$Ord$Int$meth$u$compare$0(t$e$0, t$e$1){
    
    if((t$e$0 === t$e$1)) {
        return 1;
    } else {
        
        if((t$e$0 < t$e$1)) {
            return 0;
        } else {
            return 2;
        }
    }
}

function q_2$Prelude$Interfaces$where$q_2$Prelude$Interfaces$impl_1$q_2$Prelude$Interfaces$u$Ord$Integer$meth$u$compare$0(t$e$0, t$e$1){
    
    if(t$e$0.equals(t$e$1)) {
        return 1;
    } else {
        
        if(((t$e$0).compareTo((t$e$1)) < 0)) {
            return 0;
        } else {
            return 2;
        }
    }
}

function q_2$Prelude$Interfaces$where$q_2$Prelude$Show$impl_1$q_2$Prelude$Interfaces$u$Ord$Prec$meth$u$_62__61_$0(t$e$0, t$e$1){
    let $cg$1 = null;
    if((q_2$Prelude$Interfaces$where$q_2$Prelude$Show$impl_1$q_2$Prelude$Interfaces$u$Ord$Prec$meth$u$compare$0(t$e$0, t$e$1) === 2)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    
    if($cg$1) {
        return true;
    } else {
        return q_2$Prelude$Interfaces$t$Prelude__Show___64_Prelude__Interfaces__Ord_36_Prec_58__33__62__61__58_0_95_lam$0(t$e$0, t$e$1);
    }
}

function q_2$Prelude$Interfaces$where$q_2$Prelude$Show$impl_1$q_2$Prelude$Interfaces$u$Ord$Prec$meth$u$compare$0(t$e$0, t$e$1){
    
    return q_2$Prelude$Interfaces$where$q_2$Prelude$Interfaces$impl_1$q_2$Prelude$Interfaces$u$Ord$Integer$meth$u$compare$0(q_2$Prelude$Show$u$precCon(t$e$0), q_2$Prelude$Show$u$precCon(t$e$1));
}

function t$io_95_bind$0(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w, t$in$0){
    return t$e$4(t$in$0);
}

function t$runMain$0(){
    return js_idris_force(q_1$Main$u$main()(null));
}

function t$io_95_bind$1(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w, t$in$0){
    return t$io_95_bind$0(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w, t$in$0)(u$w);
}

function t$io_95_bind$2(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w){
    return $partial_6_7$t$io_95_bind$1(t$e$0, t$e$1, t$e$2, t$e$3, t$e$4, u$w);
}


t$runMain$0();


}.call(this))