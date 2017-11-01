/**
 * Toggles a listing of idris package attributes and a shorter, nicer
 * presentation using a button group.
 */
(function() {
	function makeSwitch(switches) {
		for(var i = 0; i < switches.length; ++i) {
			switches[i].button.addEventListener("click", (function(self) {
				return function() {
					for(var i = 0; i < switches.length; ++i) {
						if(self === i) {
							switches[i].controls.classList.remove("hidden");
							switches[i].button.classList.add("is-active");
						} else {
							switches[i].controls.classList.add("hidden");
							switches[i].button.classList.remove("is-active");
						}
					}
				};
			})(i));
		}
	}

	var buttongroup = document.getElementById("pkginfo-switch").getElementsByTagName("a");

	var panel_rendered = document.getElementById("pkginfo-rendered");
	var panel_listing  = document.getElementById("pkginfo-list");

	makeSwitch([
		{ button: buttongroup[0], controls: panel_rendered },
		{ button: buttongroup[1], controls: panel_listing },
	]);

	buttongroup[0].click();
})();
