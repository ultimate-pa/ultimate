
package jdd.applet;


import java.applet.Applet;
import java.awt.BorderLayout;
import java.awt.Button;
import java.awt.Checkbox;
import java.awt.Choice;
import java.awt.Color;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.Label;
import java.awt.Panel;
import java.awt.TextArea;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
// import java.net.*;
import java.io.IOException;
import java.io.StringBufferInputStream;

import jdd.bdd.debug.BDDTrace;
import jdd.util.JDDConsole;
import jdd.util.Options;
import jdd.util.TextAreaTarget;


public class TraceApplet extends Applet implements ActionListener  {
	private TextArea msg, code;
	private Button bRun, bClear;
	private Checkbox cbVerbose;
	private Choice initialNodes;

	private final String initial_text =
		"MODULE c17\n"+
		"INPUT\n"+
		"	1gat,2gat,3gat,6gat,7gat;\n"+
		"OUTPUT\n"+
		"	22gat,23gat;\n"+
		"STRUCTURE\n"+
		"	10gat = nand(1gat, 3gat);\n"+
		"	11gat = nand(3gat, 6gat);\n"+
		"	16gat = nand(2gat, 11gat);\n"+
		"	19gat = nand(11gat, 7gat);\n"+
		"	22gat = nand(10gat, 16gat);\n"+
		"	23gat = nand(16gat, 19gat);\n"+
		"	print_bdd(23gat);\n"+
		"ENDMODULE\n";

	public TraceApplet() {
		final Color bgcolor = new Color(0xE0, 0xE0, 0xE0) ;
		setBackground( bgcolor );

		setLayout( new BorderLayout() );

		final Panel p = new Panel( new FlowLayout( FlowLayout.LEFT) );
		p.setBackground( bgcolor );
		add(p, BorderLayout.NORTH);
		p.add( bRun = new Button("Run") );
		p.add( bClear = new Button("Clear") );

		p.add( new Label("  Initial node-base") );
		p.add( initialNodes = new Choice() );
		initialNodes.add("10");
		initialNodes.add("100");
		initialNodes.add("1000");
		initialNodes.add("10000");
		initialNodes.add("100000");
		initialNodes.select(3);

		p.add( cbVerbose = new Checkbox("verbose", false));

		add(code = new TextArea(25,80), BorderLayout.CENTER);
		add(msg = new TextArea(16,80), BorderLayout.SOUTH);



		msg.setEditable(false);
		msg.setBackground( bgcolor );

		// status.setEditable(false);
		bRun.addActionListener( this );
		bClear.addActionListener( this );



		jdd.util.JDDConsole.out = new TextAreaTarget(msg) ;


		code.setFont( new Font("Monospaced", 0, 12) );
		code.setBackground( Color.yellow);
		code.setForeground( Color.red);
		code.setText(initial_text);


		msg.setText("\n       This is C17, from Yirng-An Chen's ISCAS'85 traces.\n\n");
		msg.setFont( new Font(null, 0, 10) );


	}


	@Override
	public void actionPerformed(ActionEvent e) {
		final Object src = e.getSource();
		if(src == bRun) {
			doRun();
		} else if(src == bClear) {
			doClear();
		}

	}

	// ----------------------------------
	private void doClear() {
		msg.setText("");
		// code.setText("");
	}

	private void doRun() {
		BDDTrace.verbose = Options.verbose = cbVerbose.getState();
		final StringBufferInputStream sbis = new StringBufferInputStream( code.getText() );
		final int nodes = Integer.parseInt( initialNodes.getSelectedItem() );
		try {
			final BDDTrace bt = new BDDTrace("(memory)", sbis, nodes );
		} catch(final IOException exx) {
			JDDConsole.out.println("ERROR: " + exx);
		}

	}
}
