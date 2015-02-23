package no.sintef.ict.splcatool;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import splar.core.constraints.BooleanVariable;
import splar.core.constraints.BooleanVariableInterface;
import splar.core.constraints.CNFClause;
import splar.core.constraints.CNFFormula;
import splar.core.constraints.CNFLiteral;

/**
 * Usage:
 * 
 * 1. initialize with nrid and idnr maps (these will be modified).
 * 2. call loadMainDimacs
 * 3. call moreConstraints (as often as necessary)
 * 4. call fixUnusedVariables -- will set all variables that have not been used so far in clauses to true
 * 5. get the CNFFormula with getCNF()
 * 
 * @author rhein
 *
 */
public class CnfDimacsInitMethods {

	
	
	private HashSet<String> stored;
	private Map<Integer, String> nrid;
	private Map<String, Integer> idnr;
	private CNFFormula cnf;
	private Map<String, BooleanVariableInterface> vars;

	public CnfDimacsInitMethods(Map<Integer, String> nrid, Map<String, Integer> idnr) {
		this.nrid = nrid;
		this.idnr = idnr;
	}
	
	CNFFormula getCNF() {
		return cnf;
	}
	
	public void loadMainDimacs(String dimacsFile) 
			throws IOException{
			Set<Set<Integer>> cs = new HashSet<Set<Integer>>();
			if (!(new File (dimacsFile)).exists() || (new File (dimacsFile)).isDirectory()) {
				throw new FileNotFoundException("File not found: \"" + dimacsFile+ "\"");
			}
			String filec = new FileUtility().readFileAsString(dimacsFile);
			int j = 0;
			int c_count = 0;
			int nc_count = 0;
			int p_count = 0;
			int given_p = 0;
			int given_c = 0;
			for(String line : filec.split("\n")){
				line = line.trim();
				if(line.startsWith("//") || line.isEmpty()) {
					// comment line
				} else if(line.startsWith("c")){
					//System.out.println(line);
					String nr = line.split(" ")[1].replace("$", "");
					// id is the rest
					int position_second_blank_in_line = line.indexOf(" ", 3);
					String id = line.substring(position_second_blank_in_line).trim();
					nrid.put(new Integer(nr), id);
					idnr.put(id, new Integer(nr));
					p_count++;
				}else if(line.endsWith(" 0") && !line.startsWith("p")){
					Set<Integer> c = new HashSet<Integer>();
					line = line.substring(0, line.length()-1).trim(); // Remove end 0
					for(String p : line.split(" ")){
						c.add(new Integer(p));
					}
					int oldsize = cs.size();
					cs.add(c);
					if(oldsize == cs.size()){
						nc_count++;
						/*System.out.println("Duplicate line: " + line);
						List<Set<Integer>> nns = new ArrayList<Set<Integer>>(cs);
						for(int i = 0; i < nns.size(); i++){
							if(nns.get(i).equals(c)){
								System.out.println(nns.get(i));
							}
						}
						System.exit(0);*/
					}else{
						c_count++;
					}
					j++;
				}else if(line.startsWith("p cnf")){
					given_p = new Integer(line.split(" ")[2]);
					given_c = new Integer(line.split(" ")[3]);
				}else{
					System.out.println("Error loading file due to: " + line);
					System.exit(-1);
				}
			}
			
			if(given_p != p_count || (c_count + nc_count) != given_c){
				System.out.println("Given p and c not equal with actual p and c: " + given_p + " and " + given_c + " vs " + p_count + " and " + (c_count + nc_count));
				System.exit(-1);
			}
			
			System.out.println("CNF: Given p and c: " + given_p + " and " + given_c);
			/*
			System.out.println("Features: " + p_count);
			System.out.println("Constraints: " + c_count);
			System.out.println("All constraints: " + (c_count + nc_count));
			*/
			
			// Write CNF
			vars = new HashMap<String, BooleanVariableInterface>();
			stored = new HashSet<String>();
			CNFFormula cnf = new CNFFormula();
			for(Set<Integer> clause : cs){
				CNFClause cl = new CNFClause();
				
				//System.out.println("Clause: " + clause);
			
				for(Integer p : clause){
					boolean isNegative = (p<0);
					BooleanVariableInterface bv = null;
					if(vars.get(nrid.get(Math.abs(p))) == null){
						//System.out.println(nrid.get(Math.abs(p)));
						bv = new BooleanVariable(nrid.get(Math.abs(p)));
						vars.put(nrid.get(Math.abs(p)), bv);
					}else{
						bv = vars.get(nrid.get(Math.abs(p)));
					}
					stored.add(bv.getID());
					CNFLiteral l = new CNFLiteral(bv, !isNegative);
					cl.addLiteral(l);
				}
				cnf.addClause(cl);
			}
			
			// Add the remaining vars
	/*		System.out.println(stored.size());
			System.out.println(nrid.values().size());
	*/		
		this.cnf = cnf;
	}
	public void loadMoreConstraints(String constraintsFile) throws IOException {
		/*
		BooleanVariableInterface f1 = vars.get("F1");
		BooleanVariableInterface f2 = vars.get("F2");
		BooleanVariableInterface f3 = vars.get("F3");
		if (f3 == null)  {
			f3 = new BooleanVariable("F3");
			vars.put("F3", f3);
		}

		CNFClause cl = new CNFClause();
		cl.addLiteral(new CNFLiteral(f1, true));
		cl.addLiteral(new CNFLiteral(f3, true));
		cnf.addClause(cl);
		*/

		if (!(new File (constraintsFile)).exists() || (new File (constraintsFile)).isDirectory()) {
			throw new FileNotFoundException("File not found: \"" + constraintsFile + "\"");
		} else {
			System.out.println("loading additional constraints: " + constraintsFile);
		}
		Map<String, Integer> mcidnr = new HashMap<String, Integer>();
		Map<Integer, String> mcnrid = new HashMap<Integer, String>();

		Set<Set<Integer>> cs = new HashSet<Set<Integer>>();
		String filec = new FileUtility().readFileAsString(constraintsFile);
		int j = 0;
		int c_count = 0;
		int nc_count = 0;
		int p_count = 0;
		int given_p = 0;
		int given_c = 0;
		for(String line : filec.split("\n")){
			line = line.trim();
			if(line.startsWith("//") || line.isEmpty()) {
				// comment line
			} else if(line.startsWith("c") && line.split(" ").length==3) {
				//System.out.println(line);
				String nr = line.split(" ")[1].replace("$", "");
				String id = line.split(" ")[2];
				mcnrid.put(new Integer(nr), id);
				mcidnr.put(id, new Integer(nr));
				p_count++;
			}else if(line.endsWith(" 0")){
				Set<Integer> c = new HashSet<Integer>();
				line = line.substring(0, line.length()-1).trim(); // Remove end 0
				for(String p : line.split(" ")){
					c.add(new Integer(p));
				}
				int oldsize = cs.size();
				cs.add(c);
				if(oldsize == cs.size()){
					nc_count++;
				}else{
					c_count++;
				}
				j++;
			}else if(line.startsWith("p cnf")){
				given_p = new Integer(line.split(" ")[2]);
				given_c = new Integer(line.split(" ")[3]);
			}else{
				System.out.println("Error loading file due to: " + line);
				System.exit(-1);
			}
		}
		/*// dont care, I dont want to always set the clause count while testing
		if(given_p != p_count || (c_count + nc_count) != given_c){
			System.out.println("Given p and c not equal with actual p and c: " + given_p + " and " + given_c + " vs " + p_count + " and " + (c_count + nc_count));
			System.exit(-1);
		}
		*/
		System.out.println("CNF: Given p and c: " + given_p + " and " + given_c);

		// Write CNF
		for(Set<Integer> clause : cs){
			CNFClause cl = new CNFClause();

			//System.out.println("Clause: " + clause);

			for(Integer p : clause){
				boolean isNegative = (p<0);
				BooleanVariableInterface bv = null;
				if(vars.get(mcnrid.get(Math.abs(p))) == null) {
					if (mcnrid.get(Math.abs(p)) == null) {
						throw new IOException("error while loading dimacs clause: " + clause + " variable " + Math.abs(p) + " is not defined.");
					}
					bv = new BooleanVariable(mcnrid.get(Math.abs(p)));
					vars.put(mcnrid.get(Math.abs(p)), bv);
				} else {
					bv = vars.get(mcnrid.get(Math.abs(p)));
				}
				stored.add(bv.getID());
				CNFLiteral l = new CNFLiteral(bv, !isNegative);
				cl.addLiteral(l);
			}
			try {
				this.cnf.addClause(cl);
			} catch (Exception e) {
				System.out.println("problem while adding clause " + cl + " (" + clause + ")");
				throw e;
			}
		}

		// Add the remaining vars
		for(String x : this.nrid.values()){
			if(!stored.contains(x)){
				BooleanVariableInterface bv = new BooleanVariable(x);
				vars.put(x, bv);
			}
		}
	}
	/**
	 * this adds all variables that have not been used so far as mandatory.
	 */
	public void makeUnusedVarsMandatory() {
		for(String x : nrid.values()) {
			if(!stored.contains(x)) {
				BooleanVariableInterface bv = new BooleanVariable(x);
				vars.put(x, bv);
				CNFClause cl = new CNFClause();
				CNFLiteral l1 = new CNFLiteral(bv, true);
				CNFLiteral l2 = new CNFLiteral(bv, true);
				cl.addLiteral(l1);
				cl.addLiteral(l2);
				cnf.addClause(cl);
			}
		}
	}
	/**
	 * this adds clauses for all variables that have not been used so far.
	 * The clause says "A or !A" so that the semantics of the model is not changed but the variable is used.
	 */
	public void addTrueOrFalseClausesForUnusedVars() {
		for(String x : nrid.values()) {
			if(!stored.contains(x)) {
				BooleanVariableInterface bv = new BooleanVariable(x);
				vars.put(x, bv);
				CNFClause cl = new CNFClause();
				CNFLiteral l1 = new CNFLiteral(bv, true);
				CNFLiteral l2 = new CNFLiteral(bv, false);
				cl.addLiteral(l1);
				cl.addLiteral(l2);
				cnf.addClause(cl);
			}
		}
	}

}
