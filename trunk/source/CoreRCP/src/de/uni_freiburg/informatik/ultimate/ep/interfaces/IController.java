package de.uni_freiburg.informatik.ultimate.ep.interfaces;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;

/**
 * This is the interface that all plugins providing a user interface to Ultimate
 * should implement. UltimateCore should always use methods in this interface,
 * and if necessary, extend it to request user interaction.
 * 
 * @author dietsch
 * 
 */
public interface IController extends IUltimatePlugin {

	/**
	 * {@link UltimateCore} initializes a controller during startup with this
	 * callback. This call delegates control to the controller.
	 * 
	 * @param core
	 *            The active {@link UltimateCore} instance that can be used by
	 *            the controller to start various Ultimate functions.
	 * @return
	 */
	int init(ICore core);

	/**
	 * Here the controller tells the caller what parser to use. Usually, the
	 * core will try to determine that automatically. This should only be called
	 * if that is not possible and hence the user's opinion is needed.
	 * 
	 * @param parser
	 *            providing parsers
	 * @return what parser should be used null if the toolchain should be
	 *         interrupted
	 */
	ISource selectParser(Collection<ISource> parser);

	/**
	 * Here the controller tells the caller what toolchain to use.
	 * 
	 * @param tools
	 *            available tools
	 * @return the desired toolchain as instance of Toolchain
	 */
	Toolchain selectTools(List<ITool> tools);

	/**
	 * Here the controller tells the caller (usually the core) what model out of
	 * a set of model ids the user has chosen.
	 * 
	 * @param modelNames
	 * @return string with model id
	 */
	List<String> selectModel(List<String> modelNames);

	/**
	 * Should be called to notify the user that the toolchain proved the program
	 * to be incorrect
	 */
	void displayToolchainResultProgramIncorrect();

	/**
	 * Should be called to notify the user that the toolchain proved the program
	 * to be correct
	 */
	void displayToolchainResultProgramCorrect();

	/**
	 * Should be called to notify the user that the toolchain failed to prove
	 * the program correct or incorrect
	 */
	void displayToolchainResultProgramUnknown(String description);

	/**
	 * Is called by the core if the controller should display an exception to
	 * the user
	 * 
	 * @param description
	 * @param ex
	 */
	void displayException(String description, Throwable ex);

}
