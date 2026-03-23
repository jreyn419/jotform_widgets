#!/usr/bin/env node
/**
 * fetch_page.js — Fetch a fully rendered web page and output its HTML to stdout.
 * Used by ems_inventory_editor.py for JS-rendered LEMSA sites.
 *
 * Usage: node fetch_page.js <url>
 * Output: Full rendered HTML to stdout
 *
 * Requires: npm install puppeteer (one-time, downloads bundled Chromium)
 */

const url = process.argv[2];
if (!url) {
  process.stderr.write("Usage: node fetch_page.js <url>\n");
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
    await page.goto(url, { waitUntil: "networkidle2", timeout: 30000 });
    // Extra wait for lazy-loaded content
    await new Promise(r => setTimeout(r, 3000));
    const html = await page.content();
    process.stdout.write(html);
  } catch (err) {
    process.stderr.write(err.message + "\n");
    process.exit(1);
  } finally {
    if (browser) await browser.close();
  }
})();
