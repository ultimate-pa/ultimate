
package jdd.applet;

import java.applet.*;
import java.awt.*;
import java.awt.event.*;


import jdd.examples.*;
import jdd.util.*;


/** Applet interface for the N Queens problem and its solvers */

public class QueensApplet extends Applet implements ActionListener  {
	private TextArea msg;
	private Button bSolve, bClear;
	private Choice cSize, cSolver;
	private Checkbox cbVerbose;

	public QueensApplet() {
		Color bgcolor = new Color(0xE0, 0xE0, 0xE0) ;
		setBackground( bgcolor );
		setLayout( new BorderLayout() );

		Panel p = new Panel( new FlowLayout( FlowLayout.LEFT) );
		p.setBackground( bgcolor );
		add(p, BorderLayout.NORTH);
		p.add( bSolve = new Button("Solve!") );
		p.add( bClear = new Button("Clear") );


		p.add( new Label("        N = ") );
		p.add( cSize= new Choice() );
		for(int i = 4; i < 14;i++) cSize.add("" + i	);
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

	public void actionPerformed(ActionEvent e) {
		Object src = e.getSource();
		if(src == bSolve) doSolve();
		else if(src == bClear) doClear();
	}

	// ----------------------------------
	private void doClear() {		msg.setText("");	}

	private Queens getSolver(int n) {
		JDDConsole.out.println("Loading solver '" + cSolver.getSelectedItem()  + "'...");

		int type = cSolver.getSelectedIndex();
		switch(type) {
			case 0: return new BDDQueens( n);
			case 1: return new ZDDQueens( n);
			case 2: return new ZDDCSPQueens( n);
		}
		return null; // ERROR
	}

	private void doSolve() {
		try {
			int n = Integer.parseInt ( cSize.getSelectedItem() );

			Options.verbose = cbVerbose.getState();
			Queens q = getSolver( n);
			boolean [] sol = q.getOneSolution();
			JDDConsole.out.println("" + q.numberOfSolutions() + " solutions /" + q.getTime() + "ms");
			if(sol != null)  new QueensBoard(sol);
		} catch(Exception exx) {
			JDDConsole.out.println("Failed: " + exx.toString() );
			exx.printStackTrace();
			// throw exx;
		}
	}
}
