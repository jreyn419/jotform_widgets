#!/usr/bin/env node
/**
 * fetch_page.js — Fetch web content via a real browser (Puppeteer).
 * Used by ems_inventory_editor.py for JS-rendered LEMSA sites.
 *
 * Usage:
 *   node fetch_page.js <url>              — render page, output HTML to stdout
 *   node fetch_page.js --download <url>   — download file, output base64 to stdout
 *
 * Requires: npm install puppeteer (one-time, downloads bundled Chromium)
 */

const args = process.argv.slice(2);
const downloadMode = args[0] === "--download";
const url = downloadMode ? args[1] : args[0];

if (!url) {
  process.stderr.write("Usage: node fetch_page.js [--download] <url>\n");
  process.exit(1);
}

(async () => {
  let browser;
  try {
    const puppeteer = require("puppeteer");
    browser = await puppeteer.launch({
      headless: true,
      args: ["--no-sandbox", "--disable-setuid-sandbox"]
    });
    const page = await browser.newPage();
    await page.setUserAgent(
      "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) " +
      "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
    );

    if (downloadMode) {
      // Use in-page fetch to get raw bytes, avoiding Chrome's PDF viewer
      // First navigate to the origin to establish cookies/session
      const urlObj = new URL(url);
      await page.goto(urlObj.origin, { waitUntil: "domcontentloaded", timeout: 15000 }).catch(() => {});
      
      // Now fetch the actual file from within the page context
      const b64 = await page.evaluate(async (fileUrl) => {
        const resp = await fetch(fileUrl);
        if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
        const buf = await resp.arrayBuffer();
        const bytes = new Uint8Array(buf);
        let binary = "";
        for (let i = 0; i < bytes.length; i++) {
          binary += String.fromCharCode(bytes[i]);
        }
        return btoa(binary);
      }, url);
      
      process.stdout.write(b64);
    } else {
      await page.goto(url, { waitUntil: "networkidle2", timeout: 30000 });
      await new Promise(r => setTimeout(r, 3000));
      const html = await page.content();
      process.stdout.write(html);
    }
  } catch (err) {
    process.stderr.write(err.message + "\n");
    process.exit(1);
  } finally {
    if (browser) await browser.close();
  }
})();
