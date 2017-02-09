
'use strict';

var fs = require('fs');
var mkdirp = require('mkdirp');
var parse = require('csv-parse/lib/sync');
var yaml = require('js-yaml');

function getCSVData(fileName) {
  var csvString = fs.readFileSync('../_data/' + fileName, 'utf8');
  return parse(csvString, {columns: true}); // http://csv.adaltas.com/parse/examples/#using-the-synchronous-api
}

function getYAMLData(fileName) {
  var yamlString = fs.readFileSync('../_data/' + fileName, 'utf8');
  return yaml.safeLoad(yamlString);
}

function getJSONData(fileName) {
  var jsonString = fs.readFileSync('../_data/' + fileName, 'utf8');
  return JSON.parse(jsonString);
}

function createMarkdownFile(writePath, data) {

  // https://www.npmjs.com/package/js-yaml#safedump-object---options-
  var output =
`---
${yaml.safeDump(data)}
---
`;

  // console.log(writePath + '/' +  filename + '.md');

  mkdirp(writePath, function (err) {
    if (err) {
      console.error(err);
    } else {
      fs.writeFileSync(writePath + '/' + data.name.toLowerCase().replace(/\s/g, '-') + '.md', output, 'utf8', (err) => {
        if (err) {
          console.log(err);
        }
      });
    }
  });
}

function generateCollection() {

  var writePath = '../_state';
  var states = getCSVData('states.csv');
  for (let index = 0; index < states.length; index++) {
    createMarkdownFile(writePath, states[index]);
  }
  
}

generateCollection();
