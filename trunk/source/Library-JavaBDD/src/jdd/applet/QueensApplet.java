
package jdd.applet;

import java.applet.Applet;
import java.awt.BorderLayout;
import java.awt.Button;
import java.awt.Checkbox;
import java.awt.Choice;
import java.awt.Color;
import java.awt.FlowLayout;
import java.awt.Label;
import java.awt.Panel;
import java.awt.TextArea;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import jdd.examples.BDDQueens;
import jdd.examples.Queens;
import jdd.examples.ZDDCSPQueens;
import jdd.examples.ZDDQueens;
import jdd.util.JDDConsole;
import jdd.util.Options;
import jdd.util.TextAreaTarget;


/** Applet interface for the N Queens problem and its solvers */

public class QueensApplet extends Applet implements ActionListener  {
	private TextArea msg;
	private Button bSolve, bClear;
	private Choice cSize, cSolver;
	private Checkbox cbVerbose;

	public QueensApplet() {
		final Color bgcolor = new Color(0xE0, 0xE0, 0xE0) ;
		setBackground( bgcolor );
		setLayout( new BorderLayout() );

		final Panel p = new Panel( new FlowLayout( FlowLayout.LEFT) );
		p.setBackground( bgcolor );
		add(p, BorderLayout.NORTH);
		p.add( bSolve = new Button("Solve!") );
		p.add( bClear = new Button("Clear") );


		p.add( new Label("        N = ") );
		p.add( cSize= new Choice() );
		for(int i = 4; i < 14;i++) {
			cSize.add("" + i	);
		}
		cSize.select(5);


		p.add( new Label("        Solver: ") );
		p.add( cSolver = new Choice() );
		cSolver.add("BDD");
		cSolver.add("ZDD");
		cSolver.add("ZDD-CSP");

		p.add( cbVerbose = new Checkbox("Verbose") );

		add(msg = new TextArea(10,80), BorderLayout.CENTER);
		msg.setEditable(false);
		msg.setBackground( bgcolor );

		bSolve.addActionListener( this );
		bClear.addActionListener( this );

		JDDConsole.out = new TextAreaTarget(msg) ;
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		final Object src = e.getSource();
		if(src == bSolve) {
			doSolve();
		} else if(src == bClear) {
			doClear();
		}
	}

	// ----------------------------------
	private void doClear() {		msg.setText("");	}

	private Queens getSolver(int n) {
		JDDConsole.out.println("Loading solver '" + cSolver.getSelectedItem()  + "'...");

		final int type = cSolver.getSelectedIndex();
		switch(type) {
			case 0: return new BDDQueens( n);
			case 1: return new ZDDQueens( n);
			case 2: return new ZDDCSPQueens( n);
		}
		return null; // ERROR
	}

	private void doSolve() {
		try {
			final int n = Integer.parseInt ( cSize.getSelectedItem() );

			Options.verbose = cbVerbose.getState();
			final Queens q = getSolver( n);
			final boolean [] sol = q.getOneSolution();
			JDDConsole.out.println("" + q.numberOfSolutions() + " solutions /" + q.getTime() + "ms");
			if(sol != null) {
				new QueensBoard(sol);
			}
		} catch(final Exception exx) {
			JDDConsole.out.println("Failed: " + exx.toString() );
			exx.printStackTrace();
			// throw exx;
		}
	}
}
