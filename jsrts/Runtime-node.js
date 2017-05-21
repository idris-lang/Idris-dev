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
