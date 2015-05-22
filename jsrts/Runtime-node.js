var i$putStr = (function() {
  var fs = require('fs');
  return function(s) {
    fs.write(1,s);
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
