package local.stalin.interactiveconsole;

import local.stalin.core.coreplugin.toolchain.ToolchainJob;

/**
 * Statement that allows to run the most recent toolchain
 * with the most recent boogie file.
 * 
 * @author Christian Simon
 *
 */
public class RerunStmt extends Stmt {

	@Override
	public void execute() {
		ToolchainJob tcj = new ToolchainJob("Processing Toolchain", 
				this.controller.getCore(), null, null, ToolchainJob.Chain_Mode.RERUN_TOOLCHAIN, null);
		tcj.schedule();
		try {
			tcj.join();
		} catch (InterruptedException e) {
			System.err.println("Exception in toolchain.");
			return;
		}
	}

}
