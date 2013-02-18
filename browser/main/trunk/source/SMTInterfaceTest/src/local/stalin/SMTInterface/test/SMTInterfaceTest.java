package local.stalin.SMTInterface.test;

import java.io.File;
import java.io.FileReader;
import java.io.Reader;
import java.util.Collections;

import local.stalin.SMTInterface.Activator;
import local.stalin.SMTInterface.SMTInterface;
import local.stalin.SMTInterface.test.InterpolantChecker.IncorrectInterpolantException;
import local.stalin.SMTInterface.viewer.ProofTreeInput;
import local.stalin.SMTInterface.viewer.ProofTreeEditor;
import local.stalin.core.api.StalinServices;
import local.stalin.ep.interfaces.ISource;
import local.stalin.logic.Formula;
import local.stalin.model.GraphType;
import local.stalin.model.INode;
import local.stalin.model.TokenMap;
import local.stalin.model.GraphType.Type;
import local.stalin.nativez3.Z3ProofRule;
import local.stalin.smt.smtlib.Benchmark;
import local.stalin.smt.smtlib.Lexer;
import local.stalin.smt.smtlib.MySymbolFactory;
import local.stalin.smt.smtlib.Parser;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;

public class SMTInterfaceTest implements ISource {
	
	private Logger mlogger;
	
	public SMTInterfaceTest() {
		mlogger = StalinServices.getInstance().getLoggerForExternalTool("SMTInterface");
        // ALL | DEBUG | INFO | WARN | ERROR | FATAL | OFF:
        mlogger.setLevel(Level.ALL);
	}
	
	private final static String[] gfiletypes = { "smt" }; 
	
	@Override
	public String[] getFileTypes() {
		return gfiletypes;
	}

	@SuppressWarnings("unchecked")
	@Override
	public GraphType getOutputDefinition() {
		// Dummy!!!
		return new GraphType(Activator.PLUGIN_ID,Type.OTHER,Collections.EMPTY_LIST);
	}

	@Override
	public TokenMap getTokenMap() {
		// Does not return a token map!!!
		return null;
	}

	@Override
	public String[] getTokens() {
		// Does not return tokens!!!
		return null;
	}

	@Override
	public INode parseAST(File[] files) throws Exception {
		// Only single files supported!!!
		return null;
	}

	@Override
	public INode parseAST(final File file) throws Exception {
		MySymbolFactory symfactory = new MySymbolFactory();
		Reader reader;
		reader = new FileReader(file);
		Lexer lexer = new Lexer(reader);
		lexer.setSymbolFactory(symfactory);
		Parser parser = new Parser(lexer, symfactory);
		parser.setFileName(file.getName());
		mlogger.debug("Starting SMTLIB Parser");
		Benchmark b = (Benchmark) parser.parse().value;
		mlogger.debug("SMTLIB Parser finished");
		final IntHolder ih = new IntHolder();
		final Display display = PlatformUI.getWorkbench().getDisplay();
		display.syncExec(new Runnable() {
			
			@Override
			public void run() {
				InputDialog id = new InputDialog(display.getActiveShell(),"Solver?","0 = SMTLIB, 1 = SMTINTERPOL, 2 = Z3_SIMPLIFY, 3 = Z3_NATIVE, 4 = Z3_NATIVE_INTERPOL, 5 = GROUNDIFY","0",new IInputValidator() {

					@Override
					public String isValid(String newText) {
						try {
							int val = Integer.parseInt(newText);
							return 0 <= val && val < 6 ? null : "Select value between 0 and 5";
						} catch( Exception e ) {
							return e.getMessage();
						}
					}
				
				});
				id.setBlockOnOpen(true);
				if( id.open() == InputDialog.OK )
					ih.val = Integer.parseInt(id.getValue());
				else 
					ih.val = -1;
			}
		
		});
		if( ih.val != -1 ) {
			mlogger.debug("User selected solver " + ih.val);
			SMTInterface iface = new SMTInterface(b.getTheory(),ih.val);
			Formula[] forms = b.getFormulae().toArray(new Formula[b.getFormulae().size()]);
			if (iface.isInterpolating() && forms.length > 1) {
				mlogger.info("Trying to compute interpolants");
				Formula[] interpolants = iface.computeInterpolants(forms,null);
				if( interpolants != null ) {
					mlogger.info("Formula is unsat!");
					InterpolantChecker ic = new InterpolantChecker(b.getTheory(),forms);
					for( Formula f : interpolants )
						mlogger.info("Interpolant: " + f.toString());
					try {
						ic.checkInterpolants(interpolants);
						mlogger.info("All Interpolants are correct!");
					} catch( IncorrectInterpolantException iie ) {
						mlogger.error("Incorrect Interpolant", iie);
					}
				} else
					mlogger.info("Formula is sat/unknown!");
			} else {
				// Non-interpolating solver:
				Formula conj = forms[0];
				for (int i = 1; i < forms.length; ++i)
					conj = b.getTheory().and(conj, forms[i]);
				int res = iface.checkSatisfiable(conj);
				switch (res) {
				case SMTInterface.SMT_SAT:
					mlogger.info("Formula is sat");
					break;
				case SMTInterface.SMT_UNSAT:
					mlogger.info("Formula is unsat");
					break;
				case SMTInterface.SMT_UNKNOWN:
					mlogger.info("Cannot determine satisfiability!");
					break;
				case SMTInterface.SMT_ERROR:
					mlogger.info("Something bad happened!!!");
					break;
				}
			}
			if( ih.val >= SMTInterface.SOLVER_Z3_NATIVE && ih.val != SMTInterface.SOLVER_GROUNDIFY ) {
				final Z3ProofRule root = iface.z3proof();
				System.err.println("Proof root is " + root);
				if( root != null ) {
					System.err.println("Creating UI Job");
					UIJob job = new UIJob("Jung Graph View Display") {
						public IStatus runInUIThread(IProgressMonitor mon) {
							// here we are in UI-thread so we can call
							IWorkbenchWindow window = PlatformUI.getWorkbench()
								.getActiveWorkbenchWindow();
							try {
								window.getActivePage().openEditor(new ProofTreeInput(root,file.getName()),
										ProofTreeEditor.ID, true);
							} catch (PartInitException pie) {
								MessageDialog.openError(window.getShell(), "Error",
										"Error opening Z3 Proof Visualization:\n" + pie.getMessage());
								return Status.CANCEL_STATUS;
							} catch (Exception ex) {
								ex.printStackTrace(System.err);
								return Status.CANCEL_STATUS;
							}
							return Status.OK_STATUS;
						}
					};
					job.setPriority(UIJob.INTERACTIVE); // the fastest execution possible.
					job.schedule(); // start job.
				}// root != null
			}// Z3 Native solver
		}// Invalid selection
//		System.err.println(b.getTheory().getFunctions());
//		System.err.println(b.getTheory().getPredicates());
		return null;
	}

	@Override
	public boolean parseable(File[] files) {
		// Only single files supported!!!
		return false;
	}

	@Override
	public boolean parseable(File file) {
		return file.getName().endsWith(gfiletypes[0]);
	}

	@Override
	public String getName() {
		return "SMTInterface Test Parser and Interpolator";
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public int init(Object params) {
		// No Op
		return 0;
	}

	private static final class IntHolder {
		int val;
	}

	@Override
	public void setPreludeFile(File prelude) {
		// Nothing to do here...
	}
	
}
