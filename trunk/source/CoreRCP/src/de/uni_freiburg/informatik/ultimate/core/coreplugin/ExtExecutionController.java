/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.apache.log4j.Logger;
import org.eclipse.equinox.app.IApplication;
import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.api.PreludeProvider;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.Toolchain;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.ToolchainJob;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IController;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ICore;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool;

/**
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 13.03.2012
 */
public class ExtExecutionController implements IController {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	/**
	 * The given Toolchain-File.
	 */
	private Toolchain tc;
	/**
	 * The given Input-File.
	 */
	private File inputFile;

	public ExtExecutionController(String toolchain, File inputFile) {
		try {
			this.tc = new Toolchain(toolchain);
			this.inputFile = inputFile;
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (JAXBException e) {
			e.printStackTrace();
		} catch (SAXException e) {
			e.printStackTrace();
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#init(java
	 * .lang.Object)
	 */
	@Override
	public int init(Object param) {
		ICore core;
		if (!(param instanceof ICore)) {
			return -1;
		} else {
			core = (ICore) param;
		}

		try {
			ToolchainJob tcj = new ToolchainJob("Processing Toolchain", core,
					this, this.inputFile,
					ToolchainJob.Chain_Mode.RUN_TOOLCHAIN, new PreludeProvider(
							""));
			tcj.schedule();
			// in non-GUI mode, we must wait until job has finished!
			tcj.join();
		} catch (InterruptedException e) {
			s_Logger.error("Exception in Toolchain", e);
			return -1;
		}

		return IApplication.EXIT_OK;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getName()
	 */
	@Override
	public String getName() {
		return Activator.s_PLUGIN_NAME;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IRCPPlugin#getPluginID
	 * ()
	 */
	@Override
	public String getPluginID() {
		return Activator.s_PLUGIN_ID;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectParser
	 * (java.util.Collection)
	 */
	@Override
	public ISource selectParser(Collection<ISource> parser) {
		throw new UnsupportedOperationException(
				"This Method should never be called for this controller!");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectTools
	 * (java.util.List)
	 */
	@Override
	public Toolchain selectTools(List<ITool> tools) {
		return this.tc;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#selectModel
	 * (java.util.List)
	 */
	@Override
	public List<String> selectModel(List<String> modelNames) {
		ArrayList<String> returnList = new ArrayList<String>();
		for (String model : modelNames) {
			if (model.contains("CACSL2BoogieTranslator")) {
				returnList.add(model);
			}
		}
		if (returnList.isEmpty()) {
			returnList.addAll(modelNames);
		}
		return returnList;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#getLoadPrefName
	 * ()
	 */
	@Override
	public String getLoadPrefName() {
		throw new UnsupportedOperationException(
				"This Method should never be called for this controller!");
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.ep.interfaces.IController#getSavePrefName
	 * ()
	 */
	@Override
	public String getSavePrefName() {
		throw new UnsupportedOperationException(
				"This Method should never be called for this controller!");
	}

	@Override
	public void displayToolchainResultProgramIncorrect() {
		// TODO Auto-generated method stub
	}

	@Override
	public void displayToolchainResultProgramCorrect() {
		// TODO Auto-generated method stub
	}

	@Override
	public void displayToolchainResultProgramUnknown(String description) {
		// TODO Auto-generated method stub
	}

	@Override
	public void displayException(String description, Throwable ex) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}

}
