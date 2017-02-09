
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

var statesData = getCSVData('states.csv');
var goodData = getYAMLData('opposed-good.is.yaml');
var laTimesData = getJSONData('california-latimes.com.json');

function getData(member) {

  var good_quote_html;
  for (let index = 0; index < goodData.length; index++) {
    let next = goodData[index];
    if (next.name.indexOf(member.name.last) >= 0 && next.name.indexOf(member.name.first) >= 0) {
      good_quote_html = next.html;
    }
  }

  var latimes_stance;
  var latimes_quote;
  var latimes_source;

  for (let index = 0; index < laTimesData.length; index++) {
    let next = laTimesData[index];
    if (next.Name.indexOf(member.name.last) >= 0 && next.Name.indexOf(member.name.first) >= 0) {
      latimes_stance = next.Stance;
      latimes_quote = next.Quote;
      latimes_source = next.Source;
    }
  }

  var stance = 'undecided';

  if (good_quote_html) stance = 'oppose';

  if (latimes_stance) {
    if (latimes_stance.indexOf('Against') >= 0) {
      stance = 'oppose';
    } else if (latimes_stance.indexOf('For') >= 0) {
      stance = 'support';
    }
  }

  var current_term = member.terms[member.terms.length - 1];

  var state;
  for (let index = 0; index < statesData.length; index++) {
    let next = statesData[index];
    if (next.abbreviation === current_term.state) {
      state = next.name;
    }
  }

  if (!state) console.error(new Error('unknown state: ' + current_term.state));

  var data = {
    id: member.name.official_full.toLowerCase().replace(/\s/g, '-').replace(/\./g, '').replace(/\,/g, ''),
    full_name: member.name.official_full,
    type: current_term.type === 'sen' ? 'Senator' : 'Representative',
    state: state,
    website: current_term.url,
    phone: current_term.phone,
    stance: stance
  }

  if (current_term.district) {
    data.district = current_term.district;
  }

  if (current_term.website) {
    data.website = current_term.website;
  }

  var quote_html = '';
  if (good_quote_html) {
    quote_html = good_quote_html;
  } else if (latimes_quote) {
    quote_html = 
`<blockquote>
  <p>${latimes_quote}</p>&mdash; ${latimes_source}
  <p>Sarah D. Wire, <a href="http://spreadsheets.latimes.com/where-california-congressmembers-stand-trump-order/"><span>Los Angeles Times, January 30, 2017</span></a></p>
</blockquote>
`
  }

  data.quote_html = quote_html;

  return data;
}

function generateCollection() {

  var congress = getYAMLData('congress-theunitedstates.io.yaml');
  var data = [];
  for (let index = 0; index < congress.length; index++) {
    data.push(getData(congress[index]));
  }

  data.sort(function(a, b) {

    // Sort by state
    if (a.state < b.state) {
      return -1;
    }
    if (a.state > b.state) {
      return 1;
    }

    // And then sort by type (Senators first)
    if (a.type === 'Senator' && b.type === 'Representative') {
      return -1;
    }
    if (a.type === 'Representative' && b.type === 'Senator') {
      return 1;
    }

    // And then sort by district number
    if (a.district < b.district) {
      return -1;
    }
    if (a.district > b.district) {
      return 1;
    }

    // And then sort alphabetically, by last name
    if (a.full_name < b.full_name) {
      return -1;
    }
    if (a.full_name > b.full_name) {
      return 1;
    }

    return 0;
  });

  var output = yaml.safeDump(data);

  var writePath = '../_data';
  mkdirp(writePath, function (err) {
    if (err) {
      console.error(err);
    } else {
      fs.writeFileSync(writePath + '/' + 'congress.yaml', output, 'utf8', (err) => {
        if (err) {
          console.log(err);
        }
      });
    }
  });
}

generateCollection();
