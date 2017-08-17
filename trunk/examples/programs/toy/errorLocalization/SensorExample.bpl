//#Unsafe
/* 
 * 
 * Author: Christian Schilling, Matthias Heizmann, Numair Mansur
 * Date: 2017-06-12
 * 
 * 
 */

procedure main() returns () {
  var sensor1, sensor2, temperature, i, j : int;
  var stopOnLowTemperature : bool;
  sensor1 := -1;
  sensor2 := -1;
  havoc stopOnLowTemperature;
  
  i := 1;
  while (i<10) {
    if (i == 0) {
      // havoc sensor1;
      // sensor1 := readoutsensor1()
      // havoc sensor2;
      sensor1 := 0;
      sensor2 := 0;
    }
    havoc temperature;
    if (temperature < 0) {
          if (stopOnLowTemperature) {
            return;
          }
    }
    assert (sensor1 != -1 && sensor2 != -1);
    // do some computation with sensor data
    i := i+1;
  }
}


