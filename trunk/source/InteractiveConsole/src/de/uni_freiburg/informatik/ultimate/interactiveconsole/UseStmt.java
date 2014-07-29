package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.io.File;
import java.io.FileNotFoundException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.DefaultToolchainJob;

/**
 * Statement responsible for creating/setting a toolchain and running it on a
 * boogie file.
 * 
 * @author Christian Simon
 * 
 */
class UseStmt extends Stmt {

	private String boogie_file;
	private TC chain;

	public UseStmt(TC t, String file) {
		this.boogie_file = file;
		this.chain = t;
	}

	@Override
	public void execute() {

		//TODO: Why this? It makes no sense, the core queries the controller for tools during toolchain job execution....
//		Toolchain foo = null;
//		try {
// 
////			foo = chain.getToolchain(this.controller.getTools());
//		} catch (Exception e1) {
//			System.err
//					.println("There was an error retrieving your toolchain. Please make sure that you used appropriate plugin-id indexes!");
//			return;
//		}
//		// if new toolchain not null, update it
//		// otherwise leave the old one in the controller
//		if (foo != null)
//			this.controller.setToolchain(foo);

		File boogie = new File(boogie_file);
		if (!boogie.exists() || !boogie.canRead())
			try {
				throw new FileNotFoundException(this.boogie_file);
			} catch (FileNotFoundException e) {
				System.err.println("The specified file " + this.boogie_file + " couldn't not be found or read.");
				return;
			}

		BasicToolchainJob tcj = new DefaultToolchainJob("Processing Toolchain", this.controller.getCore(),
				this.controller, BasicToolchainJob.ChainMode.DEFAULT, boogie, this.controller.getPrelude(),
				controller.getLogger());
		tcj.schedule();
		try {
			tcj.join();
		} catch (InterruptedException e) {
			System.err.println("Exception in toolchain.");
			return;
		}
	}
}
