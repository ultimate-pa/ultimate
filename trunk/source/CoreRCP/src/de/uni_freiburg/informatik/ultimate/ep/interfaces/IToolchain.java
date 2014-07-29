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
 * TODO: Comments ! 
 * 
 * @author dietsch
 * 
 */
public interface IToolchain {

	/**
	 * (Re)-initializes the plugins, the memory manager, and the benchmark. This
	 * should be called before calling
	 * {@link #processToolchain(IProgressMonitor)}.
	 * 
	 * <b> Has to be called first</b>
	 */
	public void init();

	/**
	 * Sets the file(s) that should be parsed by this {@link IToolchain}.
	 * 
	 * <b> Has to be called after {@link #init()}</b>
	 * 
	 * @param inputfiles
	 *            input files as array of File
	 */
	public void setInputFile(File inputfiles);

	/**
	 * Call to define the tools that should be used in this toolchain.
	 * 
	 * @return {@link ToolchainData} instance describing the desired tools and
	 *         their order.
	 */
	public ToolchainData makeToolSelection();

	/**
	 * Initiates a parser for the previously set input files, possibly with a
	 * special prelude file.
	 * 
	 * If this method returns false, you do not have a valid parser for the
	 * selected files.
	 * 
	 * 
	 * @param preludefile
	 *            PreludeProvider object referencing an optional prelude file
	 *            for the parser, may be 'null'
	 * @return True iff there is a usable parser for the given files and its
	 *         initialization worked. False otherwise.
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