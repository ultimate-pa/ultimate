
package jdd.applet;

import java.applet.Applet;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Label;

import jdd.Version;


/** just show the current JDD version... */

public class JDDVersion extends Applet  {

	public JDDVersion() {
		final Color bgcolor = new Color(0xE0, 0xE0, 0xE0) ;
		setBackground( bgcolor );
		setLayout( new BorderLayout() );

		add( new Label("Current JDD build# : " + Version.build), BorderLayout.NORTH );
		add( new Label("Updated " + Version.date), BorderLayout.SOUTH);
	}
}
