module.exports = {
  mode: 'jit',
  content: [
    './_includes/**/*.html',
    './_layouts/**/*.html',
    './manual/**/*.html',
    './*.html'
  ],
  theme: {
    extend: {},
  },
  plugins: [
    // require('@tailwindcss/typography'),
  ],
}
