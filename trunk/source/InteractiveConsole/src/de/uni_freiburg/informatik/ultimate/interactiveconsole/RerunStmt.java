package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;

/**
 * Statement that allows to run the most recent toolchain
 * with the most recent boogie file.
 * 
 * @author Christian Simon
  * @deprecated Seems unused. Will not be replaced if no one needs it
 */
public class RerunStmt extends Stmt {

	@Override
	public void execute() {
		BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", 
				this.controller.getCore(), null, BasicToolchainJob.ChainMode.RERUN, null, null, this.controller.getLogger());
		tcj.schedule();
		try {
			tcj.join();
		} catch (InterruptedException e) {
			System.err.println("Exception in toolchain.");
			return;
		}
	}

}
