{-# LANGUAGE PatternGuards #-}

{-
  BigInteger Javascript code taken from:
    https://github.com/peterolson/BigInteger.js
-}

module IRTS.CodegenJavaScript (codegenJavaScript) where

import Idris.AbsSyntax
import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Core.TT
import Paths_idris
import Util.System

import Control.Arrow
import Data.Char
import Data.List
import System.IO

type NamespaceName = String

idrNamespace :: NamespaceName
idrNamespace = "__IDR__"

codegenJavaScript
  :: [(Name, SDecl)]
  -> FilePath
  -> OutputType
  -> IO ()
codegenJavaScript definitions filename outputType =
  writeFile filename output
  where
    def = map (first translateNamespace) definitions

    mainLoop :: String
    mainLoop = intercalate "\n" [ "\nfunction main() {"
                                , createTailcall "__IDR__.runMain0()"
                                , "}\n\nmain();\n"
                                ]

    output :: String
    output = concat [ idrRuntime
                    , concatMap (translateModule Nothing) def
                    , mainLoop
                    ]

idrRuntime :: String
idrRuntime =
  createModule Nothing idrNamespace $ concat
    [ "__IDR__.Type = function(type) { this.type = type; };"
    , "__IDR__.Int = new __IDR__.Type('Int');"
    , "__IDR__.Char = new __IDR__.Type('Char');"
    , "__IDR__.String = new __IDR__.Type('String');"
    , "__IDR__.Integer = new __IDR__.Type('Integer');"
    , "__IDR__.Float = new __IDR__.Type('Float');"
    , "__IDR__.Forgot = new __IDR__.Type('Forgot');" 

    , "__IDR__.bigInt=function(){var e=1e7,t=7,n={positive:!1,negative:!0},r=function(e,t){var n=e.value,r=t.value,i=n.length>r.length?n.length:r.length;for(var s=0;s<i;s++)n[s]=n[s]||0,r[s]=r[s]||0;for(var s=i-1;s>=0;s--){if(n[s]!==0||r[s]!==0)break;n.pop(),r.pop()}n.length||(n=[0],r=[0]),e.value=n,t.value=r},i=function(e,s){if(typeof e=='object')return e;e+='';var u=n.positive,a=[];e[0]==='-'&&(u=n.negative,e=e.slice(1));var e=e.split('e');if(e.length>2)throw new Error('Invalid integer');if(e[1]){var f=e[1];f[0]==='+'&&(f=f.slice(1)),f=i(f);if(f.lesser(0))throw new Error('Cannot include negative exponent part for integers');while(f.notEquals(0))e[0]+='0',f=f.prev()}e=e[0],e==='-0'&&(e='0');var l=/^([1-9][0-9]*)$|^0$/.test(e);if(!l)throw new Error('Invalid integer');while(e.length){var c=e.length>t?e.length-t:0;a.push(+e.slice(c)),e=e.slice(0,c)}var h=o(a,u);return s&&r(s,h),h},s=function(e,t){var e=o(e,n.positive),t=o(t,n.positive);if(e.equals(0))throw new Error('Cannot divide by 0');var r=0;do{var i=1,s=o(e.value,n.positive),u=s.times(10);while(u.lesser(t))s=u,i*=10,u=u.times(10);while(s.lesserOrEquals(t))t=t.minus(s),r+=i}while(e.lesserOrEquals(t));return{remainder:t.value,result:r}},o=function(f,l){var c={value:f,sign:l},h={value:f,sign:l,negate:function(e){var t=e||c;return o(t.value,!t.sign)},abs:function(e){var t=e||c;return o(t.value,n.positive)},add:function(t,s){var u,a=c,f;s?(a=i(t))&&(f=i(s)):f=i(t,a),u=a.sign;if(a.sign!==f.sign)return a=o(a.value,n.positive),f=o(f.value,n.positive),u===n.positive?h.subtract(a,f):h.subtract(f,a);r(a,f);var l=a.value,p=f.value,d=[],v=0;for(var m=0;m<l.length||v>0;m++){var g=l[m]+p[m]+v;v=g>e?1:0,g-=v*e,d.push(g)}return o(d,u)},plus:function(e,t){return h.add(e,t)},subtract:function(t,r){var s=c,u;r?(s=i(t))&&(u=i(r)):u=i(t,s);if(s.sign!==u.sign)return h.add(s,h.negate(u));if(s.sign===n.negative)return h.subtract(h.negate(u),h.negate(s));if(h.compare(s,u)===-1)return h.negate(h.subtract(u,s));var a=s.value,f=u.value,l=[],p=0;for(var d=0;d<a.length;d++){a[d]-=p,p=a[d]<f[d]?1:0;var v=p*e+a[d]-f[d];l.push(v)}return o(l,n.positive)},minus:function(e,t){return h.subtract(e,t)},multiply:function(t,n){var r,s=c,u;n?(s=i(t))&&(u=i(n)):u=i(t,s),r=s.sign!==u.sign;var a=s.value,f=u.value,l=[];for(var h=0;h<a.length;h++){l[h]=[];var p=h;while(p--)l[h].push(0)}var d=0;for(var h=0;h<a.length;h++){var v=a[h];for(var p=0;p<f.length||d>0;p++){var m=f[p],g=m?v*m+d:d;d=g>e?Math.floor(g/e):0,g-=d*e,l[h].push(g)}}var y=-1;for(var h=0;h<l.length;h++){var b=l[h].length;b>y&&(y=b)}var w=[],d=0;for(var h=0;h<y||d>0;h++){var E=d;for(var p=0;p<l.length;p++)E+=l[p][h]||0;d=E>e?Math.floor(E/e):0,E-=d*e,w.push(E)}return o(w,r)},times:function(e,t){return h.multiply(e,t)},divmod:function(e,t){var r,u=c,a;t?(u=i(e))&&(a=i(t)):a=i(e,u),r=u.sign!==a.sign;if(o(u.value,u.sign).equals(0))return{quotient:o([0],n.positive),remainder:o([0],n.positive)};if(a.equals(0))throw new Error('Cannot divide by zero');var f=u.value,l=a.value,h=[],p=[];for(var d=f.length-1;d>=0;d--){var e=[f[d]].concat(p),v=s(l,e);h.push(v.result),p=v.remainder}return h.reverse(),{quotient:o(h,r),remainder:o(p,u.sign)}},divide:function(e,t){return h.divmod(e,t).quotient},over:function(e,t){return h.divide(e,t)},mod:function(e,t){return h.divmod(e,t).remainder},pow:function(e,t){var n=c,r;t?(n=i(e))&&(r=i(t)):r=i(e,n);var s=n,f=r;if(f.lesser(0))return u;if(f.equals(0))return a;var l=o(s.value,s.sign);if(f.mod(2).equals(0)){var h=l.pow(f.over(2));return h.times(h)}return l.times(l.pow(f.minus(1)))},next:function(e){var t=e||c;return h.add(t,1)},prev:function(e){var t=e||c;return h.subtract(t,1)},compare:function(e,t){var s=c,o;t?(s=i(e))&&(o=i(t,s)):o=i(e,s),r(s,o);if(s.value.length===1&&o.value.length===1&&s.value[0]===0&&o.value[0]===0)return 0;if(o.sign!==s.sign)return s.sign===n.positive?1:-1;var u=s.sign===n.positive?1:-1,a=s.value,f=o.value;for(var l=a.length-1;l>=0;l--){if(a[l]>f[l])return 1*u;if(f[l]>a[l])return-1*u}return 0},compareAbs:function(e,t){var r=c,s;return t?(r=i(e))&&(s=i(t,r)):s=i(e,r),r.sign=s.sign=n.positive,h.compare(r,s)},equals:function(e,t){return h.compare(e,t)===0},notEquals:function(e,t){return!h.equals(e,t)},lesser:function(e,t){return h.compare(e,t)<0},greater:function(e,t){return h.compare(e,t)>0},greaterOrEquals:function(e,t){return h.compare(e,t)>=0},lesserOrEquals:function(e,t){return h.compare(e,t)<=0},isPositive:function(e){var t=e||c;return t.sign===n.positive},isNegative:function(e){var t=e||c;return t.sign===n.negative},isEven:function(e){var t=e||c;return t.value[0]%2===0},isOdd:function(e){var t=e||c;return t.value[0]%2===1},toString:function(r){var i=r||c,s='',o=i.value.length;while(o--)s+=(e.toString()+i.value[o]).slice(-t);while(s[0]==='0')s=s.slice(1);s.length||(s='0');var u=i.sign===n.positive?'':'-';return u+s},toJSNumber:function(e){return+h.toString(e)},valueOf:function(e){return h.toJSNumber(e)}};return h},u=o([0],n.positive),a=o([1],n.positive),f=o([1],n.negative),l=function(e){return typeof e=='undefined'?u:i(e)};return l.zero=u,l.one=a,l.minusOne=f,l}();typeof module!='undefined'&&(module.exports=__IDR__.bigInt);"

    , "__IDR__.Tailcall = function(f) { this.f = f };"

    , "__IDR__.Con = function(i,name,vars)"
    , "{this.i = i;this.name = name;this.vars =  vars;};\n"

    ,    "__IDR__.tailcall = function(f){\n"
      ++ "var __f = f;\n"
      ++ "while (__f) {\n"
      ++ "var f = __f;\n"
      ++ "__f = null;\n"
      ++ "var ret = f();\n"
      ++ "if (ret instanceof __IDR__.Tailcall) {\n"
      ++ "__f = ret.f;"
      ++ "\n} else {\n"
      ++ "return ret;"
      ++ "\n}"
      ++ "\n}"
      ++ "\n};\n"

    , "var newline_regex =/(.*)\\n$/;\n"

    ,    "__IDR__.print = function(s){\n"
      ++ "var m = s.match(newline_regex);\n"
      ++ "console.log(m ? m[1] : s);"
      ++ "\n};\n"
    ]

createModule :: Maybe String -> NamespaceName -> String -> String
createModule toplevel modname body =
  concat [header modname, body, footer modname]
  where
    header :: NamespaceName -> String
    header modname =
      concatMap (++ "\n")
        [ "\nvar " ++ modname ++ ";"
        , "(function(" ++ modname ++ "){"
        ]

    footer :: NamespaceName -> String
    footer modname =
      let m = maybe "" (++ ".") toplevel ++ modname in
         "\n})("
      ++ m
      ++ " || ("
      ++ m
      ++ " = {})"
      ++ ");\n"

translateModule :: Maybe String -> ([String], SDecl) -> String
translateModule toplevel ([modname], decl) =
  let body = translateDeclaration modname decl in
      createModule toplevel modname body
translateModule toplevel (n:ns, decl) =
  createModule toplevel n $ translateModule (Just n) (ns, decl)

translateIdentifier :: String -> String
translateIdentifier =
  concatMap replaceBadChars
  where replaceBadChars :: Char -> String
        replaceBadChars ' '  = "_"
        replaceBadChars '_'  = "__"
        replaceBadChars '@'  = "_at"
        replaceBadChars '['  = "_OSB"
        replaceBadChars ']'  = "_CSB"
        replaceBadChars '('  = "_OP"
        replaceBadChars ')'  = "_CP"
        replaceBadChars '{'  = "_OB"
        replaceBadChars '}'  = "_CB"
        replaceBadChars '!'  = "_bang"
        replaceBadChars '#'  = "_hash"
        replaceBadChars '.'  = "_dot"
        replaceBadChars ','  = "_comma"
        replaceBadChars ':'  = "_colon"
        replaceBadChars '+'  = "_plus"
        replaceBadChars '-'  = "_minus"
        replaceBadChars '*'  = "_times"
        replaceBadChars '<'  = "_lt"
        replaceBadChars '>'  = "_gt"
        replaceBadChars '='  = "_eq"
        replaceBadChars '|'  = "_pipe"
        replaceBadChars '&'  = "_amp"
        replaceBadChars '/'  = "_SL"
        replaceBadChars '\\' = "_BSL"
        replaceBadChars '%'  = "_per"
        replaceBadChars '?'  = "_que"
        replaceBadChars '~'  = "_til"
        replaceBadChars '\'' = "_apo"
        replaceBadChars c
          | isDigit c = "_" ++ [c] ++ "_"
          | otherwise = [c]

translateNamespace :: Name -> [String]
translateNamespace (UN _)    = [idrNamespace]
translateNamespace (NS _ ns) = idrNamespace : map translateIdentifier ns
translateNamespace (MN _ _)  = [idrNamespace]

translateName :: Name -> String
translateName (UN name)   = translateIdentifier name
translateName (NS name _) = translateName name
translateName (MN i name) = translateIdentifier name ++ show i

translateQualifiedName :: Name -> String
translateQualifiedName name =
  intercalate "." (translateNamespace name) ++ "." ++ translateName name

translateConstant :: Const -> String
translateConstant (I i)   = show i
translateConstant (BI i)  = "__IDR__.bigInt('" ++ show i ++ "')"
translateConstant (Fl f)  = show f
translateConstant (Ch c)  = show c
translateConstant (Str s) = show s
translateConstant IType   = "__IDR__.Int"
translateConstant ChType  = "__IDR__.Char"
translateConstant StrType = "__IDR__.String"
translateConstant BIType  = "__IDR__.Integer"
translateConstant FlType  = "__IDR__.Float"
translateConstant Forgot  = "__IDR__.Forgot"
translateConstant c       =
  "(function(){throw 'Unimplemented Const: " ++ show c ++ "';})()"

translateParameterlist =
  map translateParameter
  where translateParameter (MN i name) = name ++ show i
        translateParameter (UN name) = name

translateDeclaration :: NamespaceName -> SDecl -> String
translateDeclaration modname (SFun name params stackSize body) =
     modname
  ++ "."
  ++ translateName name
  ++ " = function("
  ++ intercalate "," p
  ++ "){\n"
  ++ concatMap assignVar (zip [0..] p)
  ++ concatMap allocVar [numP..(numP+stackSize-1)]
  ++ "return "
  ++ translateExpression modname body
  ++ ";\n};\n"
  where 
    numP :: Int
    numP = length params

    allocVar :: Int -> String
    allocVar n = "var __var_" ++ show n ++ ";\n"

    assignVar :: (Int, String) -> String
    assignVar (n, s) = "var __var_" ++ show n ++ " = " ++ s ++ ";\n"

    p :: [String]
    p = translateParameterlist params

translateVariableName :: LVar -> String
translateVariableName (Loc i) =
  "__var_" ++ show i

translateExpression :: NamespaceName -> SExp -> String
translateExpression modname (SLet name value body) =
     "(function("
  ++ translateVariableName name
  ++ "){\nreturn "
  ++ translateExpression modname body
  ++ ";\n})("
  ++ translateExpression modname value
  ++ ")"

translateExpression _ (SConst cst) =
  translateConstant cst

translateExpression _ (SV var) =
  translateVariableName var

translateExpression modname (SApp False name vars) =
  createTailcall $ translateFunctionCall name vars

translateExpression modname (SApp True name vars) =
     "new __IDR__.Tailcall("
  ++ "function(){\n"
  ++ "return " ++ translateFunctionCall name vars
  ++ ";\n});"

translateExpression _ (SOp op vars)
  | LPlus       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LMinus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | LTimes      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | LDiv        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | LMod        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "%" lhs rhs
  | LEq         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LLt         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LLe         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | LGt         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | LGe         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs
  | LAnd        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "&" lhs rhs
  | LOr         <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "|" lhs rhs
  | LXOr        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "^" lhs rhs
  | LSHL        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<<" rhs lhs
  | LSHR        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">>" rhs lhs
  | LCompl      <- op
  , (arg:_)     <- vars = '~' : translateVariableName arg

  | LBPlus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".add(" lhs rhs  ++ ")"
  | LBMinus     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".minus(" lhs rhs ++ ")"
  | LBTimes     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".times(" lhs rhs ++ ")"
  | LBDiv       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".divide(" lhs rhs ++ ")"
  | LBMod       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".mod(" lhs rhs ++ ")"
  | LBEq        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".equals(" lhs rhs ++ ")"
  | LBLt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".lesser(" lhs rhs ++ ")"
  | LBLe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".lesserOrEquals(" lhs rhs ++ ")"
  | LBGt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".greater(" lhs rhs ++ ")"
  | LBGe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ".greaterOrEquals(" lhs rhs ++ ")"

  | LFPlus      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LFMinus     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "-" lhs rhs
  | LFTimes     <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "*" lhs rhs
  | LFDiv       <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "/" lhs rhs
  | LFEq        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LFLt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs
  | LFLe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<=" lhs rhs
  | LFGt        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">" lhs rhs
  | LFGe        <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp ">=" lhs rhs

  | LStrConcat  <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrEq      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "==" lhs rhs
  | LStrLt      <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "<" lhs rhs

  | LStrInt     <- op
  , (arg:_)     <- vars = "parseInt(" ++ translateVariableName arg ++ ")"
  | LIntStr     <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ")"
  | LIntBig     <- op
  , (arg:_)     <- vars = "__IDR__.bigint(" ++ translateVariableName arg ++ ")"
  | LBigInt     <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".valueOf()"
  | LBigStr     <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".toString()"
  | LStrBig     <- op
  , (arg:_)     <- vars = "__IDR__.bigint(" ++ translateVariableName arg ++ ")"
  | LFloatStr   <- op
  , (arg:_)     <- vars = "String(" ++ translateVariableName arg ++ ")"
  | LStrFloat   <- op
  , (arg:_)     <- vars = "parseFloat(" ++ translateVariableName arg ++ ")"
  | LIntFloat   <- op
  , (arg:_)     <- vars = translateVariableName arg
  | LFloatInt   <- op
  , (arg:_)     <- vars = translateVariableName arg
  | LChInt      <- op
  , (arg:_)     <- vars = translateVariableName arg ++ ".charCodeAt(0)"
  | LIntCh      <- op
  , (arg:_)     <- vars =
    "String.fromCharCode(" ++ translateVariableName arg ++ ")"

  | LFExp       <- op
  , (arg:_)     <- vars = "Math.exp(" ++ translateVariableName arg ++ ")"
  | LFLog       <- op
  , (arg:_)     <- vars = "Math.log(" ++ translateVariableName arg ++ ")"
  | LFSin       <- op
  , (arg:_)     <- vars = "Math.sin(" ++ translateVariableName arg ++ ")"
  | LFCos       <- op
  , (arg:_)     <- vars = "Math.cos(" ++ translateVariableName arg ++ ")"
  | LFTan       <- op
  , (arg:_)     <- vars = "Math.tan(" ++ translateVariableName arg ++ ")"
  | LFASin      <- op
  , (arg:_)     <- vars = "Math.asin(" ++ translateVariableName arg ++ ")"
  | LFACos      <- op
  , (arg:_)     <- vars = "Math.acos(" ++ translateVariableName arg ++ ")"
  | LFATan      <- op
  , (arg:_)     <- vars = "Math.atan(" ++ translateVariableName arg ++ ")"
  | LFSqrt      <- op
  , (arg:_)     <- vars = "Math.sqrt(" ++ translateVariableName arg ++ ")"
  | LFFloor     <- op
  , (arg:_)     <- vars = "Math.floor(" ++ translateVariableName arg ++ ")"
  | LFCeil      <- op
  , (arg:_)     <- vars = "Math.ceil(" ++ translateVariableName arg ++ ")"

  | LStrCons    <- op
  , (lhs:rhs:_) <- vars = translateBinaryOp "+" lhs rhs
  | LStrHead    <- op
  , (arg:_)     <- vars = translateVariableName arg ++ "[0]"
  | LStrRev     <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              v ++ "split('').reverse().join('')"
  | LStrIndex   <- op
  , (lhs:rhs:_) <- vars = let l = translateVariableName lhs
                              r = translateVariableName rhs in
                              l ++ "[" ++ r ++ "]"
  | LStrTail    <- op
  , (arg:_)     <- vars = let v = translateVariableName arg in
                              v ++ ".substr(1," ++ v ++ ".length-1)"
  where
    translateBinaryOp :: String -> LVar -> LVar -> String
    translateBinaryOp f lhs rhs =
         translateVariableName lhs
      ++ f
      ++ translateVariableName rhs

translateExpression _ (SError msg) =
  "(function(){throw \'" ++ msg ++ "\';})();"

translateExpression _ (SForeign _ _ "putStr" [(FString, var)]) =
  "__IDR__.print(" ++ translateVariableName var ++ ");"

translateExpression _ (SForeign _ _ fun args) =
     fun
  ++ "("
  ++ intercalate "," (map (translateVariableName . snd) args)
  ++ ");"

translateExpression modname (SChkCase var cases) =
     "(function(e){\n"
  ++ intercalate " else " (map (translateCase modname "e") cases)
  ++ "\n})("
  ++ translateVariableName var
  ++ ")"

translateExpression modname (SCase var cases) = 
     "(function(e){\n"
  ++ intercalate " else " (map (translateCase modname "e") cases)
  ++ "\n})("
  ++ translateVariableName var
  ++ ")"

translateExpression _ (SCon i name vars) =
  concat [ "new __IDR__.Con("
         , show i
         , ","
         , '\'' : translateQualifiedName name ++ "\',["
         , intercalate "," $ map translateVariableName vars
         , "])"
         ]

translateExpression modname (SUpdate var e) =
  translateVariableName var ++ " = " ++ translateExpression modname e

translateExpression modname (SProj var i) =
  translateVariableName var ++ ".vars[" ++ show i ++"]"

translateExpression _ SNothing = "null"

translateExpression _ e =
     "(function(){throw 'Not yet implemented: "
  ++ filter (/= '\'') (show e)
  ++ "';})()"

translateCase :: String -> String -> SAlt -> String
translateCase modname _ (SDefaultCase e) =
  createIfBlock "true" (translateExpression modname e)

translateCase modname var (SConstCase ty e)
  | ChType   <- ty = matchHelper "Char"
  | StrType  <- ty = matchHelper "String"
  | IType    <- ty = matchHelper "Int"
  | BIType   <- ty = matchHelper "Integer"
  | FlType   <- ty = matchHelper "Float"
  | Forgot   <- ty = matchHelper "Forgot"
  where
    matchHelper tyName = translateTypeMatch modname var tyName e

translateCase modname var (SConstCase cst@(BI _) e) =
  let cond = var ++ ".equals(" ++ translateConstant cst ++ ")" in
      createIfBlock cond (translateExpression modname e)

translateCase modname var (SConstCase cst e) =
  let cond = var ++ " == " ++ translateConstant cst in
      createIfBlock cond (translateExpression modname e)

translateCase modname var (SConCase a i name vars e) =
  let isCon = var ++ " instanceof __IDR__.Con"
      isI = show i ++ " == " ++ var ++ ".i"
      params = intercalate "," $ map (("__var_" ++) . show) [a..(a+length vars)]
      args = ".apply(this," ++ var ++ ".vars)"
      f b =
           "(function("
        ++ params 
        ++ "){\nreturn " ++ b ++ "\n})" ++ args
      cond = intercalate " && " [isCon, isI] in
      createIfBlock cond $ f (translateExpression modname e)

translateTypeMatch :: String -> String -> String -> SExp -> String
translateTypeMatch modname var ty exp =
  let e = translateExpression modname exp in
      createIfBlock (var
                  ++ " instanceof __IDR__.Type && "
                  ++ var ++ ".type == '"++ ty ++"'") e


createIfBlock cond e =
     "if (" ++ cond ++") {\n"
  ++ "return " ++ e
  ++ ";\n}"

createTailcall call =
  "__IDR__.tailcall(function(){return " ++ call ++ "})"

translateFunctionCall name vars =
     concat (intersperse "." $ translateNamespace name)
  ++ "."
  ++ translateName name
  ++ "("
  ++ intercalate "," (map translateVariableName vars)
  ++ ")"
