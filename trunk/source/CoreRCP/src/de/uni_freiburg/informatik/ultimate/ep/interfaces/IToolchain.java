package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import java.io.File;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.core.services.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * 
 * 
 * 
 * @author dietsch
 * 
 */
public interface IToolchain {

	/**
	 * Resets the core for processing a toolchain. It (re)-initializes the
	 * plugins, the memory manager, and the benchmark. This should be called
	 * every time before starting a new toolchain process.
	 * 
	 * <b> Has to be called first</b>
	 */
	public void resetCore();

	/**
	 * Sets the boogie file(s) on which a toolchain shall be processed.
	 * 
	 * <b> Has to be called after {@link #resetCore()}</b>
	 * 
	 * @param inputfiles
	 *            input files as array of File
	 */
	public void setInputFile(File inputfiles);

	/**
	 * Selects the toolchain to be processed by calling the selectTools method
	 * of the given controller.
	 * 
	 * @return Toolchain object denoting the desired toolchain
	 */
	public ToolchainData makeToolSelection();

	/**
	 * initiates a parser for the previously set input files
	 * 
	 * @param preludefile
	 *            PreludeProvider object referencing an optional prelude file
	 *            for the parser, may be 'null'
	 * @return true/false, depending on success of parser initialization
	 */
	public boolean initializeParser(PreludeProvider preludefile);

	/**
	 * Runs the previously select parser
	 * 
	 * @throws Exception
	 */
	public void runParser() throws Exception;

	/**
	 * If everything has been properly initiated, this method will process the
	 * set toolchain by calling {@link ToolchainWalker}.
	 * 
	 * @param monitor
	 *            instance of IProgressMonitor that can be used for progress
	 *            management, if in doubt, use 'null'
	 * @return something like Status.OK, Status.Cancel, etc.
	 * @throws Throwable
	 *             that is normally caused by some tool in the toolchain and
	 *             results in toolchain cancellation.
	 */
	public IStatus processToolchain(IProgressMonitor monitor) throws Throwable;

	public void addAST(IElement root, GraphType outputDefinition);

	public long getId();

	boolean hasInputFiles();
	
	public ToolchainData getCurrentToolchainData();

}