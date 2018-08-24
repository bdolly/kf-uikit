import resolve from 'rollup-plugin-node-resolve';
import commonjs from 'rollup-plugin-commonjs';
import postcss from 'rollup-plugin-postcss'
import babel from 'rollup-plugin-babel';
import pkg from './package.json';

export default [
    {
        input: 'src/index.js',
        external: [
          'react', 
          'react-proptypes'
        ],
        plugins: [
          resolve(),
          postcss({
            plugins: [],
            getExportNamed: false,
            getExport (id) {
              return cssExportMap[id];
            },
            extract: 'dist/styles.css',
          }),
          babel({
            exclude: 'node_modules/**'
          }),
          commonjs(),
        ],
        output: [
          { file: pkg.main, format: 'cjs' },
          { file: pkg.module, format: 'es' }
        ]
    }
];
