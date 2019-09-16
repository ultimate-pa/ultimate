package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.time.ZonedDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;

public class SMTFeatureExtractor {

	// Members
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final List<SMTFeature> mFeatures;
	private final String mDumpPath;
	private final String mFilename;

	public SMTFeatureExtractor(ILogger logger, IUltimateServiceProvider services, String dump_path) {
		mLogger = logger;
		mServices = services;
		mFeatures = new ArrayList<>();
		mDumpPath = dump_path;
		String timestamp = ZonedDateTime.now().format(DateTimeFormatter.ofPattern( "uuuu-MM-dd" ));
		mFilename = mDumpPath + timestamp + "-smtfeatures.csv"; 
		File f = new File(mFilename);
		if(!f.exists()){
		  try {
			f.createNewFile();
			try(FileWriter fw = new FileWriter(mFilename, true);
				    BufferedWriter bw = new BufferedWriter(fw);
				    PrintWriter out = new PrintWriter(bw))
				{
				    String header = SMTFeature.getCsvHeader(";");
				    out.println(header);
				} catch (IOException | IllegalAccessException e) {
					mLogger.error(e);
				}
			
		} catch (IOException e) {
			mLogger.error(e);
		}
		}else{
		  mLogger.info("SMT feature dump-file already exists.");
		}
	}

	public void extractFeature(List<Term> assertions, double time, String result) throws IllegalAccessException, IOException {
		mLogger.warn("Extracting feature..");
		SMTFeatureExtractionTermClassifier tc = new SMTFeatureExtractionTermClassifier(mLogger);
		for (Term term : assertions) {
			tc.checkTerm(term);
		}
		SMTFeature feature = new SMTFeature();
		//feature.assertionStack = tc.getTerm();
		feature.containsArrays = tc.hasArrays();
		feature.occuringFunctions = tc.getOccuringFunctionNames();
		feature.occuringQuantifiers = tc.getOccuringQuantifiers();
		feature.occuringSorts = tc.getOccuringSortNames();
		feature.numberOfFunctions = tc.getNumberOfFunctions();
		feature.numberOfQuantifiers = tc.getNumberOfQuantifiers();
		feature.numberOfVariables = tc.getNumberOfVariables();
		feature.dagsize = tc.getDAGSize();
		feature.treesize = tc.getTreeSize();
		feature.solverresult = result;
		feature.solvertime = time;
		mFeatures.add(feature);
		mLogger.warn("FEATURE: " + feature);
		dumpFeature(feature);
		
	}
	
	public void dumpFeature(SMTFeature feature) throws IllegalAccessException, IOException {
		mLogger.warn("Writing to file:" + mFilename);
		try(FileWriter fw = new FileWriter(mFilename, true);
			    BufferedWriter bw = new BufferedWriter(fw);
			    PrintWriter out = new PrintWriter(bw))
			{
			    mLogger.warn(SMTFeature.getCsvHeader(";"));
			    out.println(feature.toCsv(";"));
			} catch (IOException e) {
				throw new IOException(e);
			}
	}

}
