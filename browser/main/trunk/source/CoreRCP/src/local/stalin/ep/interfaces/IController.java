package local.stalin.ep.interfaces;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import local.stalin.core.coreplugin.toolchain.Toolchain;

/**
 * This is the interface that all plugins providing a gui or commandline
 * user interface to Stalin should adhere to.
 * 
 * 
 * @author all
 * 
 */
public interface IController extends IRCPPlugin {

	/**
	 * Here the controller tells the caller what parser to use. Usually, 
	 * the core will try to determine that automatically. This should only
	 * be called if that is not possible and hence the user's opinion is
	 * needed.
	 * 
	 * @param parser providing parsers 
	 * @return what parser should be used null if the toolchain should be
	 *         interrupted
	 */
	ISource selectParser(Collection<ISource> parser);

	/**
	 * Here the controller tells the caller what toolchain to use. 
	 * 
	 * @param tools available tools
	 * @return the desired toolchain as instance of Toolchain
	 */
	Toolchain selectTools(List<ITool> tools);
	
	
	/**
	 * Here the controller tells the caller (usually the core)
	 * what model out of a set of model ids the user has chosen.
	 * 
	 * @param modelNames
	 * @return string with model id
	 */
	List<String> selectModel(List<String> modelNames);

	String getLoadPrefName();
	
	String getSavePrefName();
	
}
