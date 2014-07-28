package de.uni_freiburg.informatik.ultimate.interactiveconsole;

import java.io.FileNotFoundException;
import java.util.List;

import javax.xml.bind.JAXBException;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainData;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * Representation for a toolchain that is obtained from an xml input file.
 * 
 * @author Christian Simon
 *
 */
public class TCfile extends TC {

	private String xml_chain;
	
	public TCfile(String file) {
		this.xml_chain = file;
	}

	@Override
	public ToolchainData getToolchain(List<ITool> tools) throws Exception {
		try {
			return new ToolchainData(this.xml_chain);
		} catch (FileNotFoundException e) {
			System.err.println("The specified file "+e.getMessage()+" couldn't be found or read.");
			return null;
		} catch (JAXBException e) {
			System.err.println("The specified file couldn't be parsed. Please check the XML syntax.");
			return null;
		}
	}
	
}
