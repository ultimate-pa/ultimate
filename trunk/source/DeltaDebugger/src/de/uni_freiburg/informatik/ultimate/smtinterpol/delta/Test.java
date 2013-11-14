package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class Test {

	/**
	 * @param args
	 * @throws InterruptedException 
	 * @throws IOException 
	 */
	public static void main(String[] args) throws IOException, InterruptedException {
		List<String> elems = new ArrayList<String>();
		for (int i = 0; i < 10; ++i)
			elems.add("" + i);
		BinSearch<String> bs = new BinSearch<String>(elems, new BinSearch.Driver<String>() {

			@Override
			public void prepare(List<String> sublist) {
				System.err.println("Prepare: " + sublist);
			}

			@Override
			public void failure(List<String> sublist) {
				System.err.println("Failure: " + sublist);
			}

			@Override
			public void success(List<String> sublist) {
				System.err.println("Success: " + sublist);
			}
			
		});
		bs.run(new Minimizer(null, 0, null, null, null) {

			@Override
			boolean test() throws IOException, InterruptedException {
				return Math.random() < 0.25;
			}
			
		});
	}

}
