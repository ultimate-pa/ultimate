
package jdd.util;

import java.util.Date;

/**
 * A Simple utility for getting time of the day
 *
 */
public class TimeUtility {
    
    /**
     *  Get time as a string YYYYMMDD-HH:mm
     * 
     * <i>I hereby predict that this code will pay for a consulant's
     * new yatch, sometime around the year 10000.</i>
     */ 
	public static String getShortTimeString() {
		final StringBuffer sb = new StringBuffer();
		final Date now = new Date();

		int tmp = now.getYear();
		if(tmp < 200) {
			tmp += 1900;
		}
		sb.append(tmp);

		tmp = now.getMonth();
		if(tmp < 10) {
			sb.append('0');
		}
		sb.append(tmp);

		tmp = now.getDay();
		if(tmp < 10) {
			sb.append('0');
		}
		sb.append(tmp);

		sb.append('-');


		tmp = now.getHours();
		if(tmp < 10) {
			sb.append('0');
		}
		sb.append(tmp);

		sb.append(':');

		tmp = now.getMinutes();
		if(tmp < 10) {
			sb.append('0');
		}
		sb.append(tmp);



		// date = ""+ now.getYear() + "" + now.getMonth() + "" + now.getDay() + ":" + now.getHours();
		return sb.toString();
	}
}