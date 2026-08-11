var codeElement = document.getElementById("code");

window.addEventListener("message", function (e) {
	if (typeof e.data !== "string") return;
	codeElement.classList.remove("empty");
	codeElement.textContent = e.data;
});

// The opening page waits for a message from us before sending the code block.
if (window.opener) {
	window.opener.postMessage("ready", "*");
} else {
	codeElement.textContent = "Open this page by clicking a DemoSAT code block.";
}
