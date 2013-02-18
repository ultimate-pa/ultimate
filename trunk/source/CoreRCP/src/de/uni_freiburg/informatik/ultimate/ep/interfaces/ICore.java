package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainWalker;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;

/**
 * This interface provides the core functionality of Ultimate for
 * processing toolchains. The methods described below make up
 * everything that one needs for this purpose. In reality,
 * only the ToolchainJob class requires them. But everyone else
 * is welcome to use them as well.
 * 
 * @author Björn Buchhold, Christian Ortolf, Christian Simon
 *
 */
public interface ICore {
	
	/**
	 * Resets the core for processing a toolchain. It (re)-initializes
	 * the plugins, the memory manager, and the benchmark. This should
	 * be called every time before starting a new toolchain process.
	 */
	void resetCore();
	
	/**
	 * Sets the boogie file(s) on which a toolchain shall be processed.
	 * 
	 * @param inputfiles input files as array of File
	 */
	void setInputFile(File inputfiles);
	
	/**
	 * Selects the toolchain to be processed by calling the selectTools method of the given controller. 
	 * 
	 * @return Toolchain object denoting the desired toolchain
	 */
	Toolchain makeToolSelection();
	
	/**
	 * initiates a parser for the previously set input files
	 * 
	 * @param preludefile PreludeProvider object referencing an optional prelude file for the parser, may be 'null' 
	 * @return true/false, depending on success of parser initialization 
	 */
	boolean initiateParser(PreludeProvider preludefile);
	
	/**
	 * Runs the previously select parser
	 * 
	 * @throws Exception
	 */
	void letCoreRunParser() throws Exception;
	
	
	/**
	 * If everything has been properly initiated, this method will process the set toolchain
	 * by calling {@link ToolchainWalker}.
	 * 
	 * @param monitor instance of IProgressMonitor that can be used for progress management,
	 * 		  if in doubt, use 'null'
	 * @return something like Status.OK, Status.Cancel, etc.
	 * @throws Exception that is probably caused by some tool in the toolchain
	 */
	IStatus processToolchain(IProgressMonitor monitor) throws Exception;
	
	/**
	 * Check whether the core can rerun a toolchain.
	 * @return <code>true</code> if and only if the previous run can be repeated.
	 */
	boolean canRerun();

	/**
	 * Check whether the core currently stores an input file.
	 * @return <code>true</code> if and only if input files are stored in the core.
	 */
	boolean hasInputFiles();

	void setToolchain(Toolchain toolchain);
	
	void savePreferences();
	
	void loadPreferences();

	/*TODO*/void getAllPreferences();
	
}
