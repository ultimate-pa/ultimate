/**
 * 
 */
package local.stalin.ep.interfaces;

/**
 * Interface for Plugins which parse project files.
 * @author rj
 */
public interface IProjectFileParser extends IRCPPlugin{

	/**
	 * @param projectfilename Project file which should be parsed
	 * @return List of source files
	 */
	String[] parse(String projectfilename);
}
