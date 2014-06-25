var i$putStr = (function() {
  var util = require('util');
  return function(s) {
    util.print(s);
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
