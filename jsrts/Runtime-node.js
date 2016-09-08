var i$putStr = (function() {
  var fs = require('fs');
  return function(s) {
    fs.writeSync(1,s);
  };
})();

var i$getLine = (function() {
  var fs = require( "fs" )

  return function() {
    var ret = "";
    var b = new Buffer(1024);
    var i = 0;
    while(true) {
      fs.readSync(0, b, i, 1 )
      if (b[i] == 10) {
        ret = b.toString('utf8', 0, i);
        break;
      }
      i++;
      if (i == b.length) {
        nb = new Buffer (b.length*2);
        b.copy(nb)
        b = nb;
      }
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
