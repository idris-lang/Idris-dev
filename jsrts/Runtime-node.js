var i$putStr = (function() {
  var fs = require('fs');
  return function(s) {
    fs.write(1,s);
  };
})();

var i$getLine = (function() {
  var fs = require( "fs" )

  return function() {
    var ret = "";

    while(true) {
      var b = new Buffer(1);
      fs.readSync(0, b, 0, 1 )
      if (b[0] == 10)
        break;
      else
        ret += String.fromCharCode(b[0]);
    }

    return ret;
  };
})();

var i$systemInfo = function(index) {
  var os = require('os')
    switch(index) {
      case 0:
        return "node";
      case 1:
        return os.platform();
    }
  return "";
}
