#!/usr/bin/env bash

set -e

PADIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOF_SIZES="${PADIR}/proof-sizes.csv"
BUILD_TIMES="${PADIR}/build-times.csv"
PROOF_TIMES="${PADIR}/proof-times.csv"

INDEX="${PADIR}/index.html"
COMMIT="$(git rev-parse HEAD)"


# save admit count for toplevel index
NADMIT=$(find "${PADIR}/.." -name '*.v' \
           | xargs grep --ignore-case 'admit' \
           | wc -l)
echo "$NADMIT" > "${PADIR}/admit-count.txt"

function mkindex {
  cat <<EOF
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8">
  <title>Verdi Proofalytics</title>
  <style>
    html {
      font-family: sans-serif;
    }
    body {
      margin: 30px;
    }
    h1 {
      font-size: 28pt;
      color: #4b2e83;
    }
    h2 {
      font-size: 18pt;
      color: #4b2e83;
    }
    p {
      font-size: 12pt;
    }
    #nav {
      padding: 0 0 10px 10px;
      margin: 0;
    }
    #nav li {
      display: inline;
      padding-right: 15px;
    }
    .it {
      font-style: italic;
    }
    .bf {
      font-weight: bold;
    }
    .red {
      color: red;
    }
    .scroller {
      width: 98%;
      height: 400px;
      border: 1px solid #4b2e83;
      overflow: auto;
      margin-bottom: 40px;
    }
    table {
      border-spacing: 10px;
    }
    th {
      text-align: left;
      color: #4b2e83;
      border-bottom: 1px solid #4b2e83;
    }
    pre {
      line-height: 150%;
    }
    #cfg {
      margin-bottom: 40px;
    }
    .cfg-fld {
      color: #4b2e83;
      font-weight: bold;
      padding-right: 10px;
    }

    .bar {
      fill: steelblue;
    }

    .bar-label {
      text-anchor: start;
      font: 10px sans-serif;
      fill: black;
    }

    .bar-value {
      fill: white;
      font: 10px sans-serif;
      text-anchor: end;
    }

    .second-bar {
      fill: seagreen;
    }

    .axis text {
      font: 10px sans-serif;
    }

    text.axis-label {
      font: 18px sans-serif;
      text-anchor: middle;
    }

    .axis path,
    .axis line {
      fill: none;
      stroke: #000;
      shape-rendering: crispEdges;
    }
  </style>
  <script src="http://d3js.org/d3.v3.min.js" charset="utf-8"></script>
  <script>
    function drawChart(config) {
      var width = 840,
          barHeight = 20,
          axisHeight = 45,
          topMargin = 5;


      var x = d3.scale.linear()
          .range([1, width/2]);

      var xAxis = d3.svg.axis()
          .scale(x)
          .orient("top");

      var chart = d3.select(config.chartId)
          .attr("width", width);

      var body = chart.append("g")
          .attr("transform", "translate(0," + (axisHeight + topMargin)  + ")");

      function totalValue(d) {
        if (config.stacked) {
            return d[config.value] + d[config.secondValue];;
        } else {
            return d[config.value];
        }
      }

      d3.csv(config.csvFile, type, function(error, data) {
          console.log(data.slice(0,20));
          if (config.stacked) {
              data.sort(function(a,b) { return totalValue(b) - totalValue(a); });
              console.log(data.slice(0,20));
          }

          data = data.slice(0, 20);

          x.domain([1, d3.max(data, function(d) { return totalValue(d); })]);

          chart.attr("height", barHeight * data.length + axisHeight + topMargin);

          chart.append("g")
              .attr("class", "x axis")
              .attr("transform", "translate(0," + axisHeight + ")")
              .call(xAxis)
              .append("text")
                .attr("x", width / 4)
                .attr("y", -axisHeight / 1.5)
                .attr("class", "axis-label")
                .text(config.valueName);


          var bar = body.selectAll(".bargroup")
              .data(data)
            .enter().append("g")
              .attr("class", "bargroup")
              .attr("transform", function(d, i) { return "translate(0," + i * barHeight + ")"; });

          bar.append("rect")
              .attr("class", "bar")
              .attr("width", function(d) { return x(d[config.value]); })
              .attr("height", barHeight - 1);

          var barEnd = function(d) { return x(d[config.value]); }

          if (config.stacked) {
              bar.append("rect")
                  .attr("class", "second-bar")
                  .attr("x", function(d) { return x(d[config.value]); })
                  .attr("width", function(d) { return x(d[config.secondValue]); })
                  .attr("height", barHeight - 1);

              barEnd = function(d) { return x(d[config.value]) + x(d[config.secondValue]); }
          }

          bar.append("text")
              .attr("class", "bar-label")
              .attr("x", function(d) { return barEnd(d) + 5; })
              .attr("y", barHeight / 2)
              .attr("dy", ".35em")
              .text(function(d) { return d[config.label]; });
      });

      function type(d) {
        d[config.value] = +d[config.value]; // coerce to number
        if (config.stacked) {
            d[config.secondValue] = +d[config.secondValue]; // coerce to number
        }
        return d;
      }
    }
  </script>
</head>
<body>
  <h1>Verdi Proofalytics</h1>
  <ul id='nav'><li>
    <a href='#proof-times'>Proof Times</a>
  </li><li>
    <a href='#build-times'>Build Times</a>
  </li><li>
    <a href='#admits'>Admits</a>
  </li><li>
    <a href='#proof-sizes'>Proof Sizes</a>
  </li></ul>
  <table id='cfg'><tr>
    <td class='cfg-fld'>Date</td>
    <td>$(TZ="America/Los_Angeles" date)</td>
  </tr><tr>
    <td class='cfg-fld'>Host</td>
    <td>$(whoami)@$(hostname -s)</td>
  </tr><tr>
    <td class='cfg-fld'>Commit</td>
    <td>
      <a href='https://github.com/uwplse/verdi/commit/$COMMIT'>
      $COMMIT</a>
    </td>
  </tr><tr>
    <td class='cfg-fld'>Coqwc</td>
    <td>
      $(find "${PADIR}/.." -name '*.v' \
          | xargs coqwc \
          | awk -W lint=fatal \
              'END { printf("spec = %'"'"'d &nbsp; &nbsp; proof = %'"'"'d\n", $1, $2) }')
    </td>
  </tr><tr>
    <td class='cfg-fld'>Compile</td>
    <td>
      $([ -f "$BUILD_TIMES" ] &&  \
          awk -W lint=fatal \
              'BEGIN { FS = ","; tot = 0 }  \
               { tot += $2 }      \
               END { print tot " sec"}' \
              "$BUILD_TIMES")
    </td>
  </tr><tr>
    <td class='cfg-fld'>Admits</td>
    <td>$NADMIT</td>
  </tr></table>
EOF

  if [ -f "$PROOF_TIMES" ]; then
    echo "<a id='proof-times'></a>"
    echo "<h2>Proof Times</h2>"
    cat <<EOF
<svg class="chart" id="proof-times-chart"></svg>
<script>
  drawChart(
    {chartId: "#proof-times-chart",
     value: "ltac",
     stacked: true,
     secondValue: "qed",
     csvFile: "proof-times.csv",
     label: "proof",
     valueName: "Total milliseconds to prove (ltac + qed)"
  });
</script>
EOF
    echo "<div class='scroller'>"
    cat "$PROOF_TIMES" \
      | awk -W lint=fatal -v commit="$COMMIT" \
            -f "${PADIR}/proof-times-links.awk" \
      | awk -W lint=fatal -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi

  if [ -f "$BUILD_TIMES" ]; then
    echo "<a id='build-times'></a>"
    echo "<h2>Build Times</h2>"
    cat <<EOF
<svg class="chart" id="build-times-chart"></svg>
<script>
  drawChart(
    {chartId: "#build-times-chart",
     csvFile: "build-times.csv",
     value: "time",
     label: "file",
     valueName: "Total seconds to build file"
  });
</script>
EOF
    echo "<div class='scroller'>"
    cat "$BUILD_TIMES" \
      | awk -W lint=fatal -v commit="$COMMIT" \
            -f "${PADIR}/build-times-links.awk" \
      | awk -W lint=fatal -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi

  echo "<a id='admits'></a>"
  echo "<h2>Admits</h2>"
  echo -n "<div class='scroller'><pre><code>"
  find "${PADIR}/.." -name '*.v' \
    | xargs grep --context=4 \
                 --line-number \
                 --ignore-case 'admit' \
    | sed -e "s|^${PADIR}/\.\./||" \
          -e 's|^--$||' \
          -e 's|admit|<span class="bf red">admit</span>|g' \
          -e 's|Admitted|<span class="bf red">Admitted</span>|g' \
    | awk -W lint=fatal -v commit="$COMMIT" \
          -f "${PADIR}/admits-links.awk"
  echo "</code></pre></div>"

  if [ -f "$PROOF_SIZES" ]; then
    echo "<a id='proof-sizes'></a>"
    echo "<h2>Proof Sizes</h2>"
    cat <<EOF
<svg class="chart" id="proof-sizes-chart"></svg>
<script>
  drawChart(
    {chartId: "#proof-sizes-chart",
     csvFile: "proof-sizes.csv",
     value: "lines",
     label: "proof",
     valueName: "Total lines of proof"
  });
</script>
EOF
    echo "<div class='scroller'>"
    cat "$PROOF_SIZES" \
      | awk -W lint=fatal -v commit="$COMMIT" \
            -f "${PADIR}/proof-sizes-links.awk" \
      | awk -W lint=fatal -f "${PADIR}/csv-table.awk"
    echo "</div>"
  fi

  cat <<EOF
</body>
</html>
EOF
}

mkindex > "$INDEX"
