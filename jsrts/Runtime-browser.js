var i$putStr = function(s) {
  console.log(s);
};


var i$systemInfo = function(index) {
  switch(index) {
    case 0:
      return "javascript";
    case 1:
      return navigator.platform;
  }
  return "";
}
