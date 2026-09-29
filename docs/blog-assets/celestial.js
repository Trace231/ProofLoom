(() => {
  'use strict';

  const art = document.querySelector('.hero-art');
  const canvas = art?.querySelector('.celestial-field');
  const toggle = document.querySelector('.motion-toggle');
  const hero = document.querySelector('.hero');
  const picture = document.querySelector('.hero-image');
  const header = document.querySelector('.site-header');
  const headerCanvas = document.querySelector('.header-sky');
  const latticeCanvas = document.querySelector('.lattice-field');
  const headerCtx = headerCanvas?.getContext('2d');
  const latticeCtx = latticeCanvas?.getContext('2d');
  const ctx = canvas?.getContext('2d', { alpha: true });
  if (!ctx || !toggle) return;

  const reduced = matchMedia('(prefers-reduced-motion: reduce)');
  const pointer = matchMedia('(hover: hover) and (pointer: fine)');
  const tau = Math.PI * 2;
  let seed = 231;
  const random = () => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed / 4294967296;
  };
  let width = 0;
  let height = 0;
  let mobile = false;
  let visible = false;
  let paused = false;
  let frame = 0;
  let lastFrame = 0;
  let elapsed = 0;
  let stars = [];
  let dust = [];
  let targetX = 0;
  let targetY = 0;
  let parallaxX = 0;
  let parallaxY = 0;
  let core = { x: 0, y: 0, radiusX: 0, radiusY: 0 };
  let lettering = [];
  let viewportWidth = 0;
  let viewportHeight = 0;
  let headerHeight = 64;
  let reading = false;
  let headerTime = 0;
  let scrollEnergy = 0;
  let previousScroll = window.scrollY;
  let heroBottom = 0;
  let scrollScheduled = false;
  let headerStars = [];

  try { paused = sessionStorage.getItem('proofloom-motion') === 'paused'; } catch {}

  // A small pre-rendered bloom keeps the frame loop inexpensive on retina screens.
  const blooms = ['255,228,185', '207,228,248'].map(color => {
    const texture = document.createElement('canvas');
    texture.width = texture.height = 48;
    const paint = texture.getContext('2d');
    const light = paint.createRadialGradient(24, 24, 0, 24, 24, 24);
    light.addColorStop(0, `rgba(${color},.95)`);
    light.addColorStop(.08, `rgba(${color},.65)`);
    light.addColorStop(.3, `rgba(${color},.16)`);
    light.addColorStop(1, `rgba(${color},0)`);
    paint.fillStyle = light;
    paint.fillRect(0, 0, 48, 48);
    return texture;
  });

  function textClearance(x, y) {
    return lettering.some(box => x > box.left && x < box.right && y > box.top && y < box.bottom) ? .045 : 1;
  }

  function sizeCanvas(element, context, w, h) {
    if (!context) return;
    const ratio = Math.min(devicePixelRatio || 1, 2);
    element.width = Math.round(w * ratio);
    element.height = Math.round(h * ratio);
    context.setTransform(ratio, 0, 0, ratio, 0, 0);
  }

  function resize() {
    const box = art.getBoundingClientRect();
    width = box.width;
    height = box.height;
    if (!width || !height) return;
    mobile = width <= 700;
    const imageBox = picture.getBoundingClientRect();
    core = {
      x: imageBox.left - box.left + imageBox.width * .767,
      y: imageBox.top - box.top + imageBox.height * .444,
      radiusX: imageBox.width * .179,
      radiusY: imageBox.height * .355,
    };
    art.style.setProperty('--galaxy-x', `${core.x}px`);
    art.style.setProperty('--galaxy-y', `${core.y}px`);
    lettering = [...document.querySelectorAll('.hero-copy > *, .hero-meta')].map(node => {
      const text = node.getBoundingClientRect();
      return { left: (text.left - box.left - 14) / width, right: (text.right - box.left + 14) / width,
        top: (text.top - box.top - 10) / height, bottom: (text.bottom - box.top + 10) / height };
    });
    sizeCanvas(canvas, ctx, width, height);
    viewportWidth = document.documentElement.clientWidth;
    viewportHeight = window.innerHeight;
    headerHeight = header.getBoundingClientRect().height;
    sizeCanvas(headerCanvas, headerCtx, viewportWidth, headerHeight);
    sizeCanvas(latticeCanvas, latticeCtx, viewportWidth, viewportHeight);
    seed = 231;
    stars = Array.from({ length: mobile ? 62 : 158 }, (_, index) => {
      const x = .025 + random() * .95;
      const y = .055 + random() * .88;
      return {
        x, y, radius: .5 + random() * 1.05, phase: random() * tau,
        period: 2.8 + random() * 3.8, depth: .25 + random() * .75,
        tint: random() > .68 ? 1 : 0, flare: index % 9 === 0,
        clearance: textClearance(x, y),
      };
    });
    // Bright points are placed in empty sky, away from the baked-in lettering.
    if (!mobile) stars.push(
      { x: .565, y: .155, radius: 2.5, phase: .6, period: 4.2, depth: .8, tint: 1, flare: true, clearance: 1 },
      { x: .939, y: .727, radius: 2.1, phase: 2.7, period: 5, depth: .65, tint: 0, flare: true, clearance: 1 },
      { x: .642, y: .823, radius: 2.2, phase: 4.1, period: 3.6, depth: .45, tint: 0, flare: true, clearance: 1 },
      { x: .355, y: .775, radius: 1.9, phase: 1.1, period: 4.7, depth: 1, tint: 0, flare: true, clearance: 1 },
      { x: .827, y: .08, radius: 1.8, phase: 2.5, period: 3.7, depth: .7, tint: 1, flare: true, clearance: 1 },
      { x: .535, y: .43, radius: 1.7, phase: 3.6, period: 4.4, depth: .9, tint: 0, flare: true, clearance: 1 },
    );
    if (mobile) stars.push(
      { x: .82, y: .195, radius: 2, phase: .7, period: 3.8, depth: .8, tint: 1, flare: true, clearance: 1 },
      { x: .23, y: .84, radius: 1.9, phase: 2.5, period: 4.6, depth: .65, tint: 0, flare: true, clearance: 1 },
      { x: .84, y: .78, radius: 1.7, phase: 4.2, period: 3.3, depth: .45, tint: 0, flare: true, clearance: 1 },
    );
    dust = Array.from({ length: mobile ? 48 : 132 }, () => ({
      radius: .45 + random() * .85, angle: random() * tau,
      orbit: .26 + random() * .74, phase: random() * tau,
      speed: .055 + random() * .045, tint: random() > .8 ? 1 : 0,
    }));
    headerStars = Array.from({ length: mobile ? 17 : 42 }, () => ({
      x: random(), y: .13 + random() * .67, phase: random() * tau, radius: .35 + random() * .65,
    }));
    updateScroll();
    render(elapsed);
  }

  function point(x, y, radius, light, tint, flare = false) {
    if (light < .015) return;
    ctx.globalAlpha = light;
    ctx.fillStyle = tint ? '#dcecff' : '#fff0d5';
    ctx.beginPath();
    ctx.arc(x, y, radius, 0, tau);
    ctx.fill();
    if (!flare) return;
    const spread = radius * 23;
    ctx.drawImage(blooms[tint], x - spread / 2, y - spread / 2, spread, spread);
    const reach = radius * (3.5 + light * 4.5);
    ctx.globalAlpha = light * .8;
    ctx.beginPath();
    ctx.moveTo(x, y - reach);
    ctx.quadraticCurveTo(x + .55, y - .5, x + reach * .7, y);
    ctx.quadraticCurveTo(x + .55, y + .5, x, y + reach);
    ctx.quadraticCurveTo(x - .55, y + .5, x - reach * .7, y);
    ctx.quadraticCurveTo(x - .55, y - .5, x, y - reach);
    ctx.fill();
  }

  function orbitLight(coreX, coreY, radiusX, radiusY, time, orbit) {
    const angle = orbit.phase + time * orbit.speed;
    const position = theta => ({
      x: coreX + Math.cos(theta) * radiusX * orbit.scale + parallaxX * .35,
      y: coreY + Math.sin(theta) * radiusY * orbit.scale + parallaxY * .35,
    });
    const tail = .52;
    const segments = 36;
    ctx.lineCap = 'round';
    ctx.strokeStyle = orbit.tint ? '#c8e5ff' : '#f3d6a2';
    for (let i = 0; i < segments; i++) {
      const progress = i / segments;
      const theta = angle - Math.sign(orbit.speed) * tail * (1 - progress);
      const a = position(theta);
      const b = position(theta + Math.sign(orbit.speed) * tail / segments);
      const clearance = textClearance(a.x / width, a.y / height);
      ctx.globalAlpha = Math.pow(progress, 1.5) * .7 * clearance;
      ctx.lineWidth = .6 + progress * .7;
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.stroke();
    }
    const head = position(angle);
    point(head.x, head.y, mobile ? 1.3 : 1.7,
      .88 * textClearance(head.x / width, head.y / height), orbit.tint, true);
  }

  function meteor(time, cycle, offset, startX, startY, travelX, travelY) {
    const duration = 2.8;
    const passage = (time + offset) % cycle;
    if (passage > duration) return;
    const progress = passage / duration;
    const light = Math.sin(progress * Math.PI);
    const x = width * (startX + progress * travelX);
    const y = height * (startY + progress * travelY);
    const tailX = width * .105;
    const tailY = height * .055;
    const beam = ctx.createLinearGradient(x - tailX, y - tailY, x, y);
    beam.addColorStop(0, 'rgba(223,229,241,0)');
    beam.addColorStop(.65, 'rgba(218,231,249,.45)');
    beam.addColorStop(1, 'rgba(255,239,211,.95)');
    ctx.globalAlpha = light * .85;
    ctx.strokeStyle = beam;
    ctx.lineWidth = 1.1;
    ctx.beginPath();
    ctx.moveTo(x - tailX, y - tailY);
    ctx.quadraticCurveTo(x - tailX * .4, y - tailY * .35, x, y);
    ctx.stroke();
    point(x, y, mobile ? 1 : 1.6, light * .95, 0, true);
  }

  function render(time) {
    ctx.clearRect(0, 0, width, height);
    ctx.globalCompositeOperation = 'lighter';
    const motion = reduced.matches ? 0 : 1;
    for (const star of stars) {
      const glint = Math.pow((Math.sin(time / star.period * tau + star.phase) + 1) / 2, 2);
      const light = (.18 + glint * .82) * star.clearance;
      const drift = motion * Math.sin(time * .19 + star.phase) * 5;
      point(star.x * width + parallaxX * star.depth + drift,
        star.y * height + parallaxY * star.depth,
        star.radius, light, star.tint, star.flare);
    }

    const { x: coreX, y: coreY, radiusX, radiusY } = core;
    for (const grain of dust) {
      const angle = grain.angle + time * grain.speed * motion;
      const x = coreX + Math.cos(angle) * radiusX * grain.orbit + parallaxX * .23;
      const y = coreY + Math.sin(angle) * radiusY * grain.orbit + parallaxY * .23;
      const shimmer = .24 + .48 * Math.pow((Math.sin(time * .7 + grain.phase) + 1) / 2, 2);
      point(x, y, grain.radius, shimmer * textClearance(x / width, y / height), grain.tint);
    }

    if (motion) {
      const orbits = [
        { scale: 1.17, phase: 3.65, speed: .19, tint: 0 },
        { scale: .94, phase: 1.5, speed: -.145, tint: 1 },
        { scale: .72, phase: 5.2, speed: .12, tint: 0 },
      ];
      for (const orbit of orbits) orbitLight(coreX, coreY, radiusX, radiusY, time, orbit);
      if (mobile) {
        meteor(time, 9, .4, .39, .78, .54, .13);
      } else {
        meteor(time, 9, .45, .58, .07, .31, .18);
        meteor(time, 13, 8.5, .19, .73, .25, .07);
      }
    }
    ctx.globalAlpha = 1;
  }

  function tick(now) {
    if (now - lastFrame >= 1000 / 30) {
      const delta = lastFrame ? Math.min((now - lastFrame) / 1000, .1) : 0;
      lastFrame = now;
      elapsed += delta;
      parallaxX += (targetX - parallaxX) * .065;
      parallaxY += (targetY - parallaxY) * .065;
      if (visible) render(elapsed);
      if (reading) {
        headerTime += delta;
        renderHeader(headerTime);
      }
      if (scrollEnergy > .003) {
        renderLattice(elapsed);
        scrollEnergy *= .94;
      } else if (latticeCtx) latticeCtx.clearRect(0, 0, viewportWidth, viewportHeight);
    }
    frame = requestAnimationFrame(tick);
  }

  function updateMotion() {
    cancelAnimationFrame(frame);
    frame = 0;
    lastFrame = 0;
    const run = (visible || reading) && !document.hidden && !paused && !reduced.matches;
    art.dataset.motion = reduced.matches ? 'reduced' : (run && visible ? 'running' : 'paused');
    document.body.dataset.motion = reduced.matches ? 'reduced' : (paused ? 'paused' : 'running');
    toggle.hidden = reduced.matches;
    toggle.setAttribute('aria-pressed', String(paused));
    toggle.setAttribute('aria-label', paused ? 'Resume celestial animation' : 'Pause celestial animation');
    toggle.title = toggle.getAttribute('aria-label');
    if (reduced.matches) {
      parallaxX = parallaxY = targetX = targetY = 0;
      render(0);
    }
    if (paused || reduced.matches) {
      latticeCtx?.clearRect(0, 0, viewportWidth, viewportHeight);
      headerCtx?.clearRect(0, 0, viewportWidth, headerHeight);
    }
    if (run) frame = requestAnimationFrame(tick);
  }

  function renderHeader(time) {
    if (!headerCtx) return;
    const paint = headerCtx;
    paint.clearRect(0, 0, viewportWidth, headerHeight);
    for (const star of headerStars) {
      paint.globalAlpha = .15 + .4 * ((Math.sin(time * .7 + star.phase) + 1) / 2);
      paint.fillStyle = '#e2d7bd';
      paint.beginPath();
      paint.arc(star.x * viewportWidth, star.y * headerHeight, star.radius, 0, tau);
      paint.fill();
    }
    const passage = (time + .5) % 7.8;
    if (passage < 2.9) {
      const progress = passage / 2.9;
      const x = viewportWidth * (-.08 + progress * 1.22);
      const y = 9 + progress * (headerHeight - 21);
      const length = Math.min(210, viewportWidth * .32);
      const tail = paint.createLinearGradient(x - length, y - 9, x, y);
      tail.addColorStop(0, '#e6c99400');
      tail.addColorStop(.75, '#dfc99970');
      tail.addColorStop(1, '#fff3d9');
      paint.globalAlpha = Math.sin(progress * Math.PI) * .92;
      paint.strokeStyle = tail;
      paint.lineWidth = 1.1;
      paint.beginPath();
      paint.moveTo(x - length, y - 9);
      paint.lineTo(x, y);
      paint.stroke();
      paint.drawImage(blooms[0], x - 13, y - 13, 26, 26);
      paint.fillStyle = '#fff4dc';
      paint.beginPath();
      paint.arc(x, y, 1.25, 0, tau);
      paint.fill();
    }
    paint.globalAlpha = 1;
  }

  function renderLattice(time) {
    if (!latticeCtx) return;
    const paint = latticeCtx;
    paint.clearRect(0, 0, viewportWidth, viewportHeight);
    if (window.scrollY < 3) return;
    const margin = Math.max(mobile ? 15 : 28, (viewportWidth - 1180) / 2 + 16);
    paint.save();
    paint.beginPath();
    paint.rect(0, headerHeight, margin, viewportHeight);
    paint.rect(viewportWidth - margin, headerHeight, margin, viewportHeight);
    if (heroBottom > headerHeight && heroBottom < viewportHeight)
      paint.rect(0, Math.max(headerHeight, heroBottom - 130), viewportWidth, Math.min(130, heroBottom - headerHeight));
    paint.clip();
    const cell = mobile ? 38 : 64;
    const rise = cell * .54;
    const offset = (window.scrollY * .24) % (rise * 2);
    const wave = (time * 170 + window.scrollY * .5) % (viewportHeight + 300) - 150;
    for (let row = -2; row < viewportHeight / rise + 2; row++) {
      const y = row * rise - offset;
      for (let col = -1; col < viewportWidth / cell + 1; col++) {
        const x = col * cell + (row % 2 ? cell / 2 : 0);
        const crest = Math.exp(-Math.pow((y - wave + x * .16) / 110, 2));
        const dark = y < heroBottom;
        const side = x < margin || x > viewportWidth - margin;
        const band = side ? 1 : Math.max(0, Math.min(1, (y - heroBottom + 130) / 55));
        const clearance = dark ? textClearance(x / width, (y - heroBottom + height) / height) : 1;
        const alpha = scrollEnergy * (.09 + crest * .28) * band * clearance;
        paint.strokeStyle = dark ? '#d5bb86' : '#987a4a';
        paint.globalAlpha = alpha * (dark ? 1.15 : 1);
        paint.lineWidth = .65;
        paint.beginPath();
        paint.moveTo(x - cell / 2, y + rise);
        paint.lineTo(x, y);
        paint.lineTo(x + cell / 2, y + rise);
        paint.stroke();
        if ((row + col) % 3 === 0) {
          paint.globalAlpha = scrollEnergy * (.25 + crest * .65) * band * clearance;
          paint.fillStyle = dark ? '#f7deb0' : '#987a4a';
          paint.beginPath();
          const r = 1.2 + crest * 1.6;
          paint.moveTo(x, y - r);
          paint.lineTo(x + r, y);
          paint.lineTo(x, y + r);
          paint.lineTo(x - r, y);
          paint.closePath();
          paint.fill();
        }
      }
    }
    paint.restore();
    paint.globalAlpha = 1;
  }

  function updateScroll() {
    const nextReading = hero.getBoundingClientRect().bottom <= headerHeight + 65;
    heroBottom = hero.getBoundingClientRect().bottom;
    const distance = Math.abs(window.scrollY - previousScroll);
    if (distance) scrollEnergy = Math.min(1, scrollEnergy + .14 + distance / 160);
    previousScroll = window.scrollY;
    header.dataset.reading = String(nextReading);
    if (nextReading !== reading) {
      reading = nextReading;
      if (reading) headerTime = 0;
      updateMotion();
    }
    scrollScheduled = false;
  }

  toggle.addEventListener('click', () => {
    paused = !paused;
    try { sessionStorage.setItem('proofloom-motion', paused ? 'paused' : 'running'); } catch {}
    updateMotion();
  });
  art.addEventListener('pointermove', event => {
    if (!pointer.matches || reduced.matches || paused) return;
    const box = art.getBoundingClientRect();
    targetX = ((event.clientX - box.left) / box.width - .5) * 18;
    targetY = ((event.clientY - box.top) / box.height - .5) * 12;
  }, { passive: true });
  art.addEventListener('pointerleave', () => { targetX = targetY = 0; });
  document.addEventListener('visibilitychange', updateMotion);
  reduced.addEventListener('change', updateMotion);
  window.addEventListener('scroll', () => {
    if (!scrollScheduled) {
      scrollScheduled = true;
      requestAnimationFrame(updateScroll);
    }
  }, { passive: true });
  const headingObserver = new IntersectionObserver(entries => {
    for (const entry of entries) {
      if (entry.isIntersecting && !paused && !reduced.matches) entry.target.classList.add('crystal-enter');
      else entry.target.classList.remove('crystal-enter');
    }
  }, { rootMargin: '-12% 0px -12% 0px', threshold: .15 });
  document.querySelectorAll('.article h2').forEach(heading => headingObserver.observe(heading));
  picture.addEventListener('load', resize);
  document.fonts?.ready.then(resize);
  new IntersectionObserver(entries => {
    visible = entries[0].isIntersecting;
    updateMotion();
  }, { threshold: 0 }).observe(art);
  new ResizeObserver(resize).observe(art);
  resize();
  updateMotion();
})();
