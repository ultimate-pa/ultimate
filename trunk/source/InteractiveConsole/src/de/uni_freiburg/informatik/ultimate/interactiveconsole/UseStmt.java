package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.io.File;
import java.io.FileNotFoundException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainJob;

/**
 * Statement responsible for creating/setting a toolchain and running it on a boogie file.
 * 
 * @author Christian Simon
 *
 */
class UseStmt extends Stmt {
	
	private String boogie_file;
	private TC chain;
	
	public UseStmt (TC t, String file) {
		this.boogie_file = file;
		this.chain = t;
	}

	@Override
	public void execute() {
		Toolchain foo = null;
		try {
			foo = chain.getToolchain(this.controller.getTools());
		} catch (Exception e1) {
			System.err.println("There was an error retrieving your toolchain. Please make sure that you used appropriate plugin-id indexes!");
			return;
		}
		// if new toolchain not null, update it
		// otherwise leave the old one in the controller
		if (foo != null) 
			this.controller.setToolchain(foo);
		
		File boogie = new File(boogie_file);
		if (!boogie.exists() || !boogie.canRead())
			try {
				throw new FileNotFoundException(this.boogie_file);
			} catch (FileNotFoundException e) {
				System.err.println("The specified file "+this.boogie_file+" couldn't not be found or read.");
				return;
			}
		
		ToolchainJob tcj = new ToolchainJob("Processing Toolchain", 
				this.controller.getCore(), null, boogie, ToolchainJob.Chain_Mode.RUN_TOOLCHAIN, this.controller.getPrelude());
		tcj.schedule();
		try {
			tcj.join();
		} catch (InterruptedException e) {
			System.err.println("Exception in toolchain.");
			return;
		}
	}
}
