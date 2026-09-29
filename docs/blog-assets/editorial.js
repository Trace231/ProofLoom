(() => {
  'use strict';
  const nav = document.querySelector('.site-header nav');
  const links = [...nav.querySelectorAll('a')];
  const indicator = document.createElement('span');
  indicator.className = 'nav-indicator';
  indicator.setAttribute('aria-hidden', 'true');
  nav.append(indicator);
  let hovered = null;
  function moveIndicator() {
    const focused = links.includes(document.activeElement) && document.activeElement.matches(':focus-visible') ? document.activeElement : null;
    const link = hovered || focused || nav.querySelector('[aria-current]');
    if (!link || !link.getClientRects().length) { indicator.style.opacity = '0'; return; }
    const padding = parseFloat(getComputedStyle(link).paddingLeft) || 0;
    indicator.style.transform = 'translateX(' + (link.offsetLeft + padding) + 'px)';
    indicator.style.width = Math.max(0, link.offsetWidth - padding) + 'px';
    indicator.style.opacity = '1';
  }
  for (const link of links) link.addEventListener('pointerenter', () => { hovered = link; moveIndicator(); });
  nav.addEventListener('pointerleave', () => { hovered = null; moveIndicator(); });
  nav.addEventListener('focusin', moveIndicator);
  nav.addEventListener('focusout', () => queueMicrotask(moveIndicator));
  document.addEventListener('proofloom:reading', moveIndicator);
  new ResizeObserver(moveIndicator).observe(nav);
  document.fonts?.ready.then(moveIndicator);
  moveIndicator();

  const viewer = document.querySelector('.figure-viewer');
  if (!viewer?.showModal) return;
  const image = viewer.querySelector('.viewer-image');
  const stage = viewer.querySelector('.viewer-stage');
  const title = viewer.querySelector('#viewer-title');
  const original = viewer.querySelector('.viewer-original');
  const zoomButton = viewer.querySelector('.viewer-zoom');
  let zoomed = false;
  let opener = null;
  function setZoom(value) {
    zoomed = value;
    stage.classList.toggle('is-zoomed', value);
    zoomButton.setAttribute('aria-pressed', String(value));
    zoomButton.textContent = value ? 'Fit to screen ⤢' : 'Actual size ＋';
    if (value) {
      stage.style.setProperty('--figure-width', image.naturalWidth + 'px');
      stage.scrollLeft = Math.max(0, (stage.scrollWidth - stage.clientWidth) / 2);
      stage.scrollTop = Math.max(0, (stage.scrollHeight - stage.clientHeight) / 2);
    } else stage.scrollTo(0, 0);
  }
  document.querySelectorAll('.figure-link').forEach(link => {
    link.addEventListener('click', event => {
      if (event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
      event.preventDefault();
      const figure = link.closest('figure');
      const source = link.querySelector('img');
      opener = link;
      const number = document.createElement('span');
      number.className = 'viewer-number';
      number.textContent = String(figure.dataset.figureNumber).padStart(2, '0');
      title.replaceChildren(number, document.createTextNode(figure.dataset.figureTitle));
      image.src = link.href;
      image.alt = source.alt;
      original.href = link.href;
      setZoom(false);
      document.body.classList.add('figure-is-open');
      viewer.showModal();
    });
  });
  viewer.querySelector('.viewer-close').addEventListener('click', () => viewer.close());
  viewer.addEventListener('click', event => {
    if (event.target === viewer || event.target === stage) viewer.close();
  });
  viewer.addEventListener('close', () => {
    document.body.classList.remove('figure-is-open');
    setZoom(false);
    opener?.focus({ preventScroll: true });
  });
  zoomButton.addEventListener('click', () => { if (image.complete && image.naturalWidth) setZoom(!zoomed); });
  image.addEventListener('click', () => { if (image.complete && image.naturalWidth) setZoom(!zoomed); });
})();
