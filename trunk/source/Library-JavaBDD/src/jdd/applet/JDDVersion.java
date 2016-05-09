
package jdd.applet;

import java.applet.*;
import java.awt.*;

import jdd.*;


/** just show the current JDD version... */

public class JDDVersion extends Applet  {

	public JDDVersion() {
		Color bgcolor = new Color(0xE0, 0xE0, 0xE0) ;
		setBackground( bgcolor );
		setLayout( new BorderLayout() );

		add( new Label("Current JDD build# : " + Version.build), BorderLayout.NORTH );
		add( new Label("Updated " + Version.date), BorderLayout.SOUTH);
	}
}
