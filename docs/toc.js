// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded affix "><a href="Introduction.html">Foundations in Lean</a></li><li class="chapter-item expanded affix "><li class="part-title">Basics</li><li class="chapter-item expanded "><a href="Lean.html"><strong aria-hidden="true">1.</strong> Overview of Lean</a></li><li class="chapter-item expanded affix "><li class="part-title">Type Theory</li><li class="chapter-item expanded "><a href="LambdaCalculus.html"><strong aria-hidden="true">2.</strong> λ-Calculus</a></li><li class="chapter-item expanded "><a href="PropositionalLogic.html"><strong aria-hidden="true">3.</strong> Propositional Logic</a></li><li class="chapter-item expanded "><a href="CurryHoward.html"><strong aria-hidden="true">4.</strong> Curry-Howard Isomorphism</a></li><li class="chapter-item expanded "><a href="InductiveTypes.html"><strong aria-hidden="true">5.</strong> Inductive Types</a></li><li class="chapter-item expanded affix "><li class="part-title">Logic</li><li class="chapter-item expanded "><a href="Connectives.html"><strong aria-hidden="true">6.</strong> Propositional Connectives</a></li><li class="chapter-item expanded "><a href="FirstOrderLogic.html"><strong aria-hidden="true">7.</strong> First Order Logic</a></li><li class="chapter-item expanded "><a href="Tactics.html"><strong aria-hidden="true">8.</strong> Tactics</a></li><li class="chapter-item expanded "><a href="Equality.html"><strong aria-hidden="true">9.</strong> Equality</a></li><li class="chapter-item expanded "><a href="Relations.html"><strong aria-hidden="true">10.</strong> Sets and Relations</a></li><li class="chapter-item expanded affix "><li class="part-title">Numbers</li><li class="chapter-item expanded "><a href="Naturals/Intro.html"><strong aria-hidden="true">11.</strong> Natural Numbers</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="Naturals/Definition.html"><strong aria-hidden="true">11.1.</strong> Definition</a></li><li class="chapter-item expanded "><a href="Naturals/Properties.html"><strong aria-hidden="true">11.2.</strong> Properties</a></li></ol></li><li class="chapter-item expanded "><a href="Integers/Intro.html"><strong aria-hidden="true">12.</strong> Integers</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="Integers/Definition.html"><strong aria-hidden="true">12.1.</strong> Quotient Spaces</a></li><li class="chapter-item expanded "><a href="Integers/Operators.html"><strong aria-hidden="true">12.2.</strong> Operators</a></li><li class="chapter-item expanded "><a href="Integers/Properties.html"><strong aria-hidden="true">12.3.</strong> Properties</a></li></ol></li><li class="chapter-item expanded "><a href="Numbers.html"><strong aria-hidden="true">13.</strong> Rational Numbers</a></li><li class="chapter-item expanded "><a href="Reals.html"><strong aria-hidden="true">14.</strong> Real Numbers</a></li><li class="chapter-item expanded affix "><li class="part-title">Partial Orders</li><li class="chapter-item expanded "><a href="Ordering/Definition.html"><strong aria-hidden="true">15.</strong> Definitions</a></li><li class="chapter-item expanded "><a href="Ordering/Properties.html"><strong aria-hidden="true">16.</strong> Properties</a></li><li class="chapter-item expanded "><a href="Ordering/Maps.html"><strong aria-hidden="true">17.</strong> Maps</a></li><li class="chapter-item expanded "><a href="Ordering/Strings.html"><strong aria-hidden="true">18.</strong> Strings</a></li><li class="chapter-item expanded "><a href="Ordering/Information.html"><strong aria-hidden="true">19.</strong> Information</a></li><li class="chapter-item expanded "><a href="Ordering/Completions.html"><strong aria-hidden="true">20.</strong> The D.M. Completion</a></li><li class="chapter-item expanded affix "><li class="part-title">Appendix</li><li class="chapter-item expanded "><a href="Appendix.html"><strong aria-hidden="true">21.</strong> Helpers</a></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
