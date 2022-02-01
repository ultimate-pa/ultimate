
package jdd.internal.hashtest;



import java.awt.BorderLayout;
import java.awt.Button;
import java.awt.Choice;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.GridLayout;
import java.awt.Label;
import java.awt.Panel;
import java.awt.TextField;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import jdd.util.math.FastRandom;
import jdd.util.math.HashFunctions;


/**
 * Hash-test: for "seeing" how good the hash functions work
 */


public class HashTest extends Frame implements ActionListener, WindowListener {
	private static final int MAX_SIZE = 102400;

	private final Histogram []histograms;
	private final HistogramPanel []hp;
	private int size;
	private Button bQuit, bRun;
	private Choice cMapType, cHashType, cMixType, cSampleMulti;
	private final TextField []tfMin, tfMax;
	private TextField tfOutput, tfStatusbar;
	private final Panel []pTop;


	public HashTest () {
		super("HashTest");

		// -------------------------------
		tfMin = new TextField[3];
		tfMax = new TextField[3];
		histograms = new Histogram[4];
		hp = new HistogramPanel[4];
		pTop = new Panel[5];

		// -----------------------------------------------

		final Panel pNorth = new Panel( new GridLayout(5,1) );
		add(pNorth, BorderLayout.NORTH);


		for(int i = 0; i < 5; i++) {
			pTop[i] = new Panel( new FlowLayout( FlowLayout.LEFT) );
			pNorth.add(pTop[i]);
		}


		pTop[0].add( bQuit = new Button("Quit") );
		bQuit.addActionListener(this);

		pTop[0].add( bRun = new Button("Run test") );
		bRun.addActionListener(this);

		pTop[0].add(new Label("  Map-type:"));
		pTop[0].add(cMapType = new Choice());
		cMapType.add("1 -> 1");
		cMapType.add("2 -> 1");
		cMapType.add("3 -> 1");
		cMapType.select(2);


		pTop[0].add(new Label("  Hash:"));
		pTop[0].add(cHashType = new Choice());
		cHashType.add("pair");
		cHashType.add("prime");
		cHashType.add("Jenkins");
		cHashType.add("FNV");



		pTop[0].add(new Label("  Mix:"));
		pTop[0].add(cMixType = new Choice());
		cMixType.add("none");
		cMixType.add("simple");
		cMixType.add("Wang");
		cMixType.add("Jenkins");

		pTop[0].add(new Label("  samples = size * "));
		pTop[0].add(cSampleMulti = new Choice());
		cSampleMulti.add("17");
		cSampleMulti.add("57");
		cSampleMulti.add("111");



		// -------------------------------------------
		pTop[4].add(new Label("Output: ")) ;
		pTop[4].add(new Label("size=")) ;
		pTop[4].add(tfOutput = new TextField("128") );

		for(int i = 0; i < 3; i++) {
			final Panel p = pTop[i+1];
			p.add(new Label("Input " + i + ": ")) ;

			p.add(new Label("min=") );
			p.add( tfMin[i] = new TextField("0") );

			p.add(new Label(", max=") );
			p.add( tfMax[i] = new TextField("1000") );
		}

		// -------------------------------------------
		final Panel pCenter = new Panel( new GridLayout(4,1,2,2) );

		for(int i = 0; i < 4; i++) {
			histograms[i] = new Histogram(1000);
			pCenter.add( hp[i] = new HistogramPanel( histograms[i]) );
		}

		add(pCenter, BorderLayout.CENTER);

		add(tfStatusbar = new TextField(""), BorderLayout.SOUTH);
		tfStatusbar.setEditable(false);

		pack();
		setVisible(true);
		addWindowListener(this);
	}


	// ------[ action handlers ] -----------------------------------

	 @Override
	public void actionPerformed(ActionEvent e) {
		 final Object src = e.getSource();
		 if(src == bQuit) {
			onQuit();
		} else if(src == bRun) {
			onRun();
		}
 	}

	@Override
	public void windowActivated(WindowEvent e) { }
	@Override
	public void windowClosed(WindowEvent e) { }
	@Override
	public void windowClosing(WindowEvent e) { onQuit(); }
	@Override
	public void windowDeactivated(WindowEvent e) { }
	@Override
	public void windowDeiconified(WindowEvent e) { }
	@Override
	public void windowIconified(WindowEvent e) { }
	@Override
	public void windowOpened(WindowEvent e) { }

	// -------------------------------------------------
	private void message(String str) {
		tfStatusbar.setText( str);
	}

	private void onQuit() {
		System.exit(0);
	}

	private void onRun() {
		message("hold on...");

		final int hash_type = cHashType.getSelectedIndex();
		final int mix_type = cMixType.getSelectedIndex();

		final int inputs = 1 + cMapType.getSelectedIndex();



		if(! can_do_hash(inputs, hash_type) ) {
			message("BAD combination of inout numbers and hash function!");
			return;
		}

		final int []starts = new int[3];
		final int []widths = new int[3];
		final int []in = new int[3];

		for(int i = 0; i < inputs; i++) {
			final int s = Integer.parseInt( tfMin[i].getText() );
			final int e = Integer.parseInt( tfMax[i].getText() );
			if(s >= e || e > MAX_SIZE) {
				message("invalid or too large input"+(i+1) );
			}
			starts[i] = s;
			widths[i] = e - s;
			histograms[i].resize(widths[i]);
		}
		final int outputs = Integer.parseInt( tfOutput.getText() );
		if(outputs <2 || outputs > MAX_SIZE ) {
			message("invalid or too large output");
		}
		histograms[3].resize(outputs); // output size

		final int samples = outputs * Integer.parseInt( cSampleMulti.getSelectedItem() );
		message(" processing " + samples + " samples");



		for(int i = 0; i < samples; i++) {
			for(int j = 0; j < inputs; j++) {
				in[j] = starts[j] + (FastRandom.mtrand() % widths[j] );
				histograms[j].add( in[j] );
			}
			final int hash = do_hash(in, inputs, hash_type);
			// must be larger than 0!
			final int mixed = (do_mix(hash, mix_type) & ~0x80000000) % outputs;
			histograms[3].add( mixed);
		}

		for(int i = 0; i < 4; i++) {
			hp[i].update();
			hp[i].repaint();
		}
		message("");
	}


	private boolean can_do_hash(int in_count, int type) {
		if(in_count == 2) {
			return (type == 0 || type == 1);
		} else {
			return true;
		}
	}

	private int do_hash(int []ins, int in_count, int type) {
		if(in_count == 1) {
			return ins[0]; // no hashing, really...
		} else if(in_count == 2) {
			switch(type) {
				case 0: return HashFunctions.hash_pair(ins[0], ins[1]);
				case 1: return HashFunctions.hash_prime(ins[0], ins[1]);
				// not available for jenkins and FNV
			}
		} else if(in_count == 3) {
			switch(type) {
				case 0: return HashFunctions.hash_pair(ins[0], ins[1], ins[2]);
				case 1: return HashFunctions.hash_prime(ins[0], ins[1], ins[2]);
				case 2: return HashFunctions.hash_jenkins(ins[0], ins[1], ins[2]);
				case 3: return HashFunctions.hash_FNV(ins[0], ins[1], ins[2]);
			}
		}

		// ERROR:
		return -1;
	}
	private int do_mix(int in, int type) {
		switch(type) {
			case 1: return HashFunctions.mix(in);
			case 2: return HashFunctions.mix_wang(in);
			case 3: return HashFunctions.mix_jenkins(in);
			default:
				return in; // no mixing
		}
	}
	// -------------------------------------------------

	public static void main(String [] args) { new HashTest(); }
}
