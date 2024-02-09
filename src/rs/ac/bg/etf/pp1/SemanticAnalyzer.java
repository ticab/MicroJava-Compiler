package rs.ac.bg.etf.pp1;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.apache.log4j.Logger;

import rs.ac.bg.etf.pp1.ast.*;
import rs.etf.pp1.symboltable.*;
import rs.etf.pp1.symboltable.concepts.*;
import rs.etf.pp1.symboltable.visitors.DumpSymbolTableVisitor;
import rs.etf.pp1.symboltable.visitors.SymbolTableVisitor;

public class SemanticAnalyzer extends VisitorAdaptor {

	private Logger log = Logger.getLogger(getClass());

	private boolean errorDetected = false;
	private static int programVars = 0;
	private Struct currentType = null;
	private boolean returnFound = false;
	private Struct currNamespace = null;
	private String currNamespaceStr = null;
	private boolean namespScope = false;
	private int forCnt = 0;
	private int methodDeclParams = 0;
	private boolean isArray = false;
	private Obj currentMethod = null;
	private boolean foundMain = false;
	private int constValue;
	private Struct constType;

	private int relOp = 0;
	// 1 = EQUAL, 2 = NOT_EQ, 3 = LESS, 4 = GREATER, 5 = GREATER_EQ, 6 = LESS_EQ
	private int mulOp = 0;
	// 1 = MUL, 2 = DIV, 3 = MOD
	private int addOp = 0;
	// 1 = PLUS, 2 = MINUS

	private Stack<List<Struct>> stackActPars = new Stack<>();
	private List<Struct> listLeftDesign = new ArrayList<>();
	
	public SemanticAnalyzer() {
		Tab.currentScope.addToLocals(new Obj(Obj.Type, "bool", TabExtended.boolType));
	}

	public void printSemanticAnalyze() {
		System.out.println("=====================SYMBOL TABLE=========================");

		SymbolTableVisitor stv = new DumpSymbolTableVisitor();
		for (Scope s = Tab.currentScope(); s != null; s = s.getOuter()) {
			s.accept(stv);
		}
		log.info(stv.getOutput());
	}

	public void report_error(String message, SyntaxNode info) {
		errorDetected = true;
		StringBuilder msg = new StringBuilder("Greska");
		int line = (info == null) ? 0 : info.getLine();
		if (line != 0)
			msg.append(" na liniji ").append(line).append(": ");
		else
			msg.append(": ");
		msg.append(message);
		log.error(msg.toString());
	}

	public void report_info(String message, SyntaxNode info) {
		StringBuilder msg = new StringBuilder(message);
		int line = (info == null) ? 0 : info.getLine();
		if (line != 0)
			msg.append(" na liniji ").append(line);
		log.info(msg.toString());
	}

	public String structName(Struct s) {
		switch (s.getKind()) {
		case Struct.None:
			return "none";
		case Struct.Int:
			return "int";
		case Struct.Char:
			return "char";
		case Struct.Array:
			return "array";
		case Struct.Class:
			return "class";
		case Struct.Bool:
			return "bool";
		case Struct.Enum:
			return "enum";
		case Struct.Interface:
			return "interface";
		default:
			return "";
		}

	}

	// Program -----------------------------------------------------------------
	
	@Override
	public void visit(ProgName progName) {
		progName.obj = Tab.insert(Obj.Prog, progName.getProgName(), Tab.noType);
		Tab.openScope();
	}

	@Override
	public void visit(Program program) {
		programVars = Tab.currentScope.getnVars();
		if(!foundMain) {
			report_error("Program mora da sadrzi void main() funkciju", program);
		}
		Tab.chainLocalSymbols(program.getProgName().obj);
		Tab.closeScope();
	}

	public static int getProgramVars() {
		return programVars;
	}

	public static void setProgramVars(int programVars2) {
		programVars = programVars2;
	}
	
	// Namespace -----------------------------------------------------------------
	
	@Override
	public void visit(NamespaceName namespaceName) {
		Obj o = Tab.find(namespaceName.getNamespName());
		if(o != Tab.noObj) {
			report_error("Namespace (" + namespaceName.getNamespName() + ") mora biti jedinstven ", namespaceName);
			namespaceName.obj = Tab.noObj;
			//Tab.openScope();
			return;
		}
		currNamespaceStr = namespaceName.getNamespName();
		currNamespace = new Struct(Struct.Class);
		currNamespace.setElementType(Tab.noType);
		
		//namespaceName.obj = Tab.insert(Obj.Type, namespaceName.getNamespName(), currNamespace);
		report_info("Nov namespace: "+namespaceName.getNamespName(), namespaceName);
		//Tab.openScope();
		namespScope = true;
	}
	
	@Override
	public void visit(Namespace namespace) {
		//Tab.chainLocalSymbols(currNamespace);
		//Tab.closeScope();
		namespScope = false;
		currNamespace = null;
		currNamespaceStr = null;
	}

	// ConstDecl -----------------------------------------------------------------

	@Override
	public void visit(ConstValueEq constValueEq) {
		String constName = constValueEq.getConstName();
		if (Tab.find(constName) != Tab.noObj) {
			report_error("Ime (" + constName + ") mora biti jedinstveno", constValueEq);
			return;
		}
		String newName;
		if(namespScope)
			newName = currNamespaceStr + "::" + constValueEq.getConstName();
		else newName = constValueEq.getConstName();
		Obj constIns = Tab.insert(Obj.Con, newName, constType);
		report_info(
				"Nova konstanta:  " + structName(constType) + " " + newName + " = " + constValue,
				constValueEq);
		constIns.setAdr(constValue);
		
	}

	@Override
	public void visit(IntVal intVal) {
		if (currentType != Tab.intType) {
			report_error("Type (" + currentType + ") mora biti istog tipa kao konstanta (int)", intVal);
		}
		constValue = intVal.getNumberConstValue();
		constType = Tab.intType;
	}

	@Override
	public void visit(CharVal charVal) {
		if (currentType != Tab.charType) {
			report_error("Type (" + currentType + ") mora biti istog tipa kao konstanta (char)", charVal);
		}
		constValue = charVal.getCharConstValue();
		constType = Tab.charType;
	}

	@Override
	public void visit(BoolVal boolVal) {
		if (currentType != TabExtended.boolType) {
			report_error("Type (" + currentType + ") mora biti istog tipa kao konstanta (bool)", boolVal);
		}
		constValue = 0;
		if (boolVal.getBoolConstValue() == true)
			constValue = 1;
		constType = TabExtended.boolType;
	}

	// VarDecl -----------------------------------------------------------------

	@Override
	public void visit(VarFromMultiple varFromMultiple) {
		if (Tab.find(varFromMultiple.getVarName()) != Tab.noObj) {
			if (Tab.currentScope.findSymbol(varFromMultiple.getVarName()) != null) {
				report_error("Ime (" + varFromMultiple.getVarName() + ") promenljive mora biti jedinstveno",
						varFromMultiple);
				return;
			}
		}
		Struct typ = currentType;
		String ar = "";
		if (isArray) {
			typ = new Struct(Struct.Array, currentType);
			ar = "[]";
		}
		if(namespScope) {
			Obj var = Tab.insert(Obj.Var, currNamespaceStr + "::" + varFromMultiple.getVarName(), typ);
		}
		else {
			Obj var = Tab.insert(Obj.Var, varFromMultiple.getVarName(), typ);
		}
		
		report_info("Nova promenljiva: "+ varFromMultiple.getVarName()+ar, varFromMultiple);
		isArray = false;
	}

	@Override
	public void visit(OneVarDec oneVarDec) {
		if (Tab.find(oneVarDec.getVarName()) != Tab.noObj) {
			if (Tab.currentScope.findSymbol(oneVarDec.getVarName()) != null) {
				report_error("Ime (" + oneVarDec.getVarName() + ")promenljive mora biti jedinstveno",
						oneVarDec);
				return;
			}
		}
		Struct typ = currentType;
		String ar = "";
		if (isArray) {
			typ = new Struct(Struct.Array, currentType);
			ar = "[]";
		}
		if(namespScope) {
			Obj var = Tab.insert(Obj.Var, currNamespaceStr + "::" + oneVarDec.getVarName(), typ);
		}
		else {
			Obj var = Tab.insert(Obj.Var, oneVarDec.getVarName(), typ);
		}
		report_info("Nova promenljiva: "+ structName(typ) +" "+ oneVarDec.getVarName()+ar, oneVarDec);
		isArray = false;
	}

	// MethodDecl -----------------------------------------------------------------

	@Override
	public void visit(MethodFullName methodFullName) {
		Obj methodName = Tab.currentScope().findSymbol(methodFullName.getMethodName());
		if (methodName != null) {
			report_error("Ime metode treba da bude jedinstveno", methodFullName);
			currentMethod = Tab.noObj;
			methodFullName.obj = Tab.noObj;
			Tab.openScope();
			return;
		}
		if(namespScope)
			currentMethod = Tab.insert(Obj.Meth, currNamespaceStr + "::" + methodFullName.getMethodName(), methodFullName.getMethodReturn().struct);
		else
			currentMethod = Tab.insert(Obj.Meth, methodFullName.getMethodName(), methodFullName.getMethodReturn().struct);
		
		methodFullName.obj = currentMethod;
		Tab.openScope();
		report_info("Nova funkcija: " + structName(methodFullName.getMethodReturn().struct) + " "+ methodFullName.getMethodName(), methodFullName);
	}

	@Override
	public void visit(ReturnSomething returnSomething) {
		returnSomething.struct = currentType;
	}

	@Override
	public void visit(ReturnVoid returnVoid) {
		returnVoid.struct = Tab.noType;
	}

	@Override
	public void visit(MethodDecl methodDecl) {
		if (!returnFound && currentMethod.getType() != Tab.noType) {
			report_error("Funckija mora imati return iskaz", methodDecl);
		}
		currentMethod.setLevel(methodDeclParams);
		if (currentMethod.getLevel() == 0 && "main".equals(currentMethod.getName())) {
			foundMain = true;
		}
		Tab.chainLocalSymbols(currentMethod);
		Tab.closeScope();

		returnFound = false;
		currentMethod = null;
		methodDeclParams = 0;

	}
	// FormParams -----------------------------------------------------------------

	@Override
	public void visit(FormalParamDecl formalParamDecl) {
		methodDeclParams++;
		Obj declNode = Tab.find(formalParamDecl.getParameterName());
		if (declNode != Tab.noObj) {
			if (Tab.currentScope.findSymbol(formalParamDecl.getParameterName()) != null) {
				report_error("Parametar funkcije mora biti jedinstven", formalParamDecl);
				return;
			}
		}
		Struct paramType = currentType;
		if (isArray == true) {
			paramType = new Struct(Struct.Array, currentType);
		}
		Tab.insert(Obj.Var, formalParamDecl.getParameterName(), paramType);
		

		isArray = false;

	}

	@Override
	public void visit(IsArray isArrayV) {
		isArray = true;
	}

	// Type -----------------------------------------------------------------

	@Override
	public void visit(Type type) {
		if (Tab.find(type.getName()) == Tab.noObj) {
			report_error("Ne postoji tip (" + type.getName() + ") u tabeli simbola", type);
			type.struct = Tab.noType;
		} else if ((Tab.find(type.getName())).getKind() == Obj.Type) {
			type.struct = (Tab.find(type.getName())).getType();
		} else {
			report_error("Nepostojeci tip (" + type.getName() + ")", type);
			type.struct = Tab.noType;
		}
		currentType = type.struct;
	}

	// Statement -----------------------------------------------------------------

	@Override
	public void visit(StatementBreak statementBreak) {
		if (forCnt == 0) {
			report_error("Break se moze korisiti samo unutar for petlje", statementBreak);
		}
	}

	@Override
	public void visit(StatementContinue statementContinue) {
		if (forCnt == 0) {
			report_error("Continue se moze korisiti samo unutar for petlje", statementContinue);
		}
	}

	@Override
	public void visit(StatementReturnExpr statementReturnExpr) {
		returnFound = true;
		if (currentMethod.getType() == Tab.noType) {
			report_error("Ne sme da postoji return u void funkciji", statementReturnExpr);
			return;
		}
		if (!(currentMethod.getType()).equals(statementReturnExpr.getExpr().struct)) {
			report_error("Expr mora biti ekvivalentan povratnom tipu tekuce funkcije",
					statementReturnExpr);
			return;
		}
	}

	@Override
	public void visit(StatementRead statementRead) {
		Obj d = statementRead.getDesignator().obj;
		if (d.getKind() != Obj.Var && d.getKind() != Obj.Fld && d.getKind() != Obj.Elem) {
			report_error("Designator mora biti promenljiva/element niza/polje unutar objekta",
					statementRead);
			return;
		}
		if (d.getType() != Tab.intType && d.getType() != Tab.charType && d.getType() != TabExtended.boolType) {
			report_error("Designator (" + structName(d.getType()) + ") mora biti int/char/bool",
					statementRead);
		}
	}

	@Override
	public void visit(PrintStatement printStatement) {
		Struct e = printStatement.getExpr().struct;
		if (e != Tab.intType && e != Tab.charType && e != TabExtended.boolType) {
			report_error("Expr (" + structName(e) + ") mora biti int/char/bool", printStatement);
		}
	}

	@Override
	public void visit(PrintStatementWit printStatementWit) {
		Struct e = printStatementWit.getExpr().struct;
		if (e != Tab.intType && e != Tab.charType && e != TabExtended.boolType) {
			report_error("Expr (" + structName(e) + ") mora biti int/char/bool", printStatementWit);
		}
	}

	@Override
	public void visit(ForStatement ForStatement) {
		forCnt++;
	}

	@Override
	public void visit(StatementFor StatementFor) {
		forCnt--;
	}

	// DesignatorStatement -----------------------------------------------------------------
	@Override
	public void visit(DesignAssign designAssign) {
		Struct s = designAssign.getExpr().struct;
		Obj d = designAssign.getDesignator().obj;
		if (d.getKind() != Obj.Var && d.getKind() != Obj.Fld && d.getKind() != Obj.Elem) {
			report_error("Designator mora biti promenljiva/element niza/polje unutar objekta", designAssign);
			return;
		}
		if (!s.assignableTo(d.getType())) {
			report_error("Exp (" + structName(s) + ") mora biti kompatibilan pri dodeli sa Designator-om ("
					+ structName(d.getType()) + ")", designAssign);
		}
	}

	@Override
	public void visit(DesignFuncCall designFuncCall) {
		Obj func = designFuncCall.getFunctionCallName().obj;
		if (func.getKind() != Obj.Meth) {
			report_error("(" + func.getName() + ") mora biti funkcija", designFuncCall);
			return;
		}

		List<Struct> arguments = stackActPars.pop();

		List<Obj> declArgs = new ArrayList<Obj>();

		int i = 0;

		for (Iterator<Obj> declIt = func.getLocalSymbols().iterator(); i < func.getLevel() && declIt.hasNext();) {
			declArgs.add(declIt.next());
			i++;
		}

		int numDecl = func.getLevel();

		if (arguments.size() != numDecl) {
			report_error("Razlicit broj argumenata za funkciju", designFuncCall);
			//
			return;
		}
		for (int j = 0; j < arguments.size(); i++) {
			if (!declArgs.get(j).getType().assignableTo(arguments.get(j))) {
				report_error("Argument na poziciji (" + (j + 1) + ") treba da bude ("
						+ structName(declArgs.get(j).getType()) + "), a ne (" + structName(arguments.get(j)) + ")",
						designFuncCall);
				//
				return;
			}
		}
		report_info("Poziv funkcije: " + func.getName(), designFuncCall);
	}

	@Override
	public void visit(DesignPostInc designPostInc) {
		Obj d = designPostInc.getDesignator().obj;
		if (d.getKind() != Obj.Var && d.getKind() != Obj.Fld && d.getKind() != Obj.Elem) {
			report_error("Designator++ mora biti promenljiva/element niza/polje unutar objekta", designPostInc);
			return;
		}
		if (d.getType() != Tab.intType) {
			report_error("Designator (" + structName(d.getType()) + ")++ mora biti tipa int", designPostInc);
		}
	}

	@Override
	public void visit(DesignPostDec designPostDec) {
		Obj d = designPostDec.getDesignator().obj;
		if (d.getKind() != Obj.Var && d.getKind() != Obj.Fld && d.getKind() != Obj.Elem) {
			report_error("Designator-- mora biti promenljiva/element niza/polje unutar objekta", designPostDec);
			return;
		}
		if (d.getType() != Tab.intType) {
			report_error("Designator (" + structName(d.getType()) + ")-- mora biti tipa int", designPostDec);
		}
	}

	@Override
	public void visit(DesignBC designBC) { // *************************************
		Obj d1 = designBC.getDesignator1().obj;
		if(d1.getType().getKind() != Struct.Array) {
			report_error("Designator sa desne strane znaka za dodelu vrednosti mora predstavljati niz", designBC);
		}
		Obj d2 = designBC.getDesignator().obj;
		if(d2.getType().getKind() != Struct.Array) {
			report_error("Designator sa leve strane znaka za dodelu vrednosti mora predstavljati niz", designBC);
		}
		for(int i=0; i<listLeftDesign.size(); i++) {
			if(listLeftDesign.get(i).getKind() != Struct.Enum &&
					!d1.getType().getElemType().assignableTo(listLeftDesign.get(i))) {
				report_error("Tip elemenata niza sa desne strane = Designator ("+structName(d1.getType().getElemType())+
						") mora biti kompatibilan sa tipom svih neterminala sa leve strane osim poslednjeg greska: ("
						+structName(listLeftDesign.get(i))+")" , designBC);
			}
		}
		if(!d1.getType().assignableTo(d2.getType())){
			report_error("Nizovi Designator sa leve strane ("+structName(d1.getType().getElemType())+
					"[]) i Designator sa desne strane ("+structName(d2.getType().getElemType())+"[]) nisu istog tipa", designBC);
		}
		
		listLeftDesign.clear();
	}

	@Override
	public void visit(DesStWithDes desStWithDes) { // *************************************
		Obj d = desStWithDes.getDesignator().obj;
		if (d.getKind() != Obj.Var && d.getKind() != Obj.Fld && d.getKind() != Obj.Elem) {
			report_error("Designator sa leve strane = ,  mora biti promenljiva/element niza/polje unutar objekta",
					desStWithDes);
			return;
		}
		desStWithDes.getDesignator().obj = d;
		listLeftDesign.add(d.getType());
	}
	
	@Override
	public void visit(DesStWithComma DesStWithComma) {
		listLeftDesign.add(new Struct(6));
	}

	@Override
	public void visit(FunctionCallName functionCallName) {
		functionCallName.obj = functionCallName.getDesignator().obj;
		stackActPars.push(new ArrayList<>());
	}

	// ActPars -----------------------------------------------------------------

	@Override
	public void visit(SingleExpr singleExpr) {
		stackActPars.peek().add(singleExpr.getExpr().struct);
	}

	@Override
	public void visit(MultipleExpr multipleExpr) {
		stackActPars.peek().add(multipleExpr.getExpr().struct);
	}

	// CondFact -----------------------------------------------------------------

	@Override
	public void visit(RelopCondF relopCondF) {
		Expr e1 = relopCondF.getExpr();
		Expr e2 = relopCondF.getExpr1();

		if (!e1.struct.compatibleWith(e2.struct)) {
			report_error(
					"Expr (" + structName(e1.struct) + ") Relop Expr (" + structName(e2.struct) + ") nisu kompatibilni",
					relopCondF);
		}
		if (e1.struct.getKind() == Struct.Array || e2.struct.getKind() == Struct.Array) {
			if (relOp != 1 && relOp != 2) {
				report_error("Za poredjenje 2 niza mogu se koristiti samo != i ==", relopCondF);
			}
		}
	}

	// Expr -----------------------------------------------------------------

	@Override
	public void visit(PositiveExpr positiveExpr) {
		positiveExpr.struct = positiveExpr.getTerm().struct;
	}

	@Override
	public void visit(NegativeExpr negativeExpr) {
		if (negativeExpr.getTerm().struct != Tab.intType) {
			report_error("Term mora biti tipa int", negativeExpr);
			negativeExpr.struct = Tab.noType;
			return;
		}
		negativeExpr.struct = Tab.intType;
	}

	@Override
	public void visit(AddExpr addExpr) {
		Struct e = addExpr.getExpr().struct;
		Struct t = addExpr.getTerm().struct;
		if (!e.compatibleWith(t)) {
			report_error("Expr (" + structName(e) + ") i Term (" + structName(t) + ") moraju biti kompatibilni",
					addExpr);
			addExpr.struct = Tab.noType;
			return;
		}
		if (e != Tab.intType) {
			report_error("Expr (" + structName(e) + ") mora biti int", addExpr);
			addExpr.struct = Tab.noType;
			return;
		}
		if (t != Tab.intType) {
			report_error("Term (" + structName(t) + ") mora biti int", addExpr);
			addExpr.struct = Tab.noType;
			return;
		}
		addExpr.struct = Tab.intType;
	}

	// Term -----------------------------------------------------------------

	@Override
	public void visit(Term term) {
		term.struct = term.getFactors().struct;
	}

	// Factors -----------------------------------------------------------------

	@Override
	public void visit(OneFactor oneFactor) {
		oneFactor.struct = oneFactor.getFactor().struct;
	}
	
	@Override
	public void visit(MulFactors mulFactors) {
		if (mulFactors.getFactor().struct != Tab.intType || mulFactors.getFactors().struct != Tab.intType) {
			report_error("Cinioci moraju biti tipa int", mulFactors);
			mulFactors.struct = Tab.noType;
			return;
		}
		mulFactors.struct = Tab.intType;
	}

	// Factor -----------------------------------------------------------------

	@Override
	public void visit(FactorVar factorVar) {
		factorVar.struct = factorVar.getDesignator().obj.getType();
		if (factorVar.getDesignator().obj.getKind() == Obj.Var && factorVar.getDesignator().obj.getType().getKind() != Struct.Array) {
			report_info("Pristup promenjivoj " + factorVar.getDesignator().obj.getName(), factorVar);
		}
	}

	@Override
	public void visit(FactorFuncCall factorFuncCall) {
		Obj func = factorFuncCall.getFunctionCallName().obj;
		if (func.getKind() != Obj.Meth) {
			report_error("(" + func.getName() + ") mora biti funkcija", factorFuncCall);
			return;
		}

		List<Struct> arguments = stackActPars.pop();

		List<Obj> declArgs = new ArrayList<Obj>();

		int i = 0;

		for (Iterator<Obj> declIt = func.getLocalSymbols().iterator(); i < func.getLevel() && declIt.hasNext();) {
			declArgs.add(declIt.next());
			i++;
		}

		int numDecl = func.getLevel();

		if (arguments.size() != numDecl) {
			report_error("Razlicit broj argumenata za funkciju", factorFuncCall);
			factorFuncCall.struct = Tab.noType;
			return;
		}
		for (int j = 0; j < arguments.size(); j++) {
			if (!declArgs.get(j).getType().assignableTo(arguments.get(j))) {
				report_error("Argument na poziciji (" + (j + 1) + ") treba da bude ("
						+ structName(declArgs.get(j).getType()) + "), a ne (" + structName(arguments.get(j)) + ")",
						factorFuncCall);
				factorFuncCall.struct = Tab.noType;
				return;
			}
		}
		report_info("Poziv funkcije: " + func.getName(), factorFuncCall);
		factorFuncCall.struct = func.getType();
	}

	@Override
	public void visit(FactorNum factorNum) {
		factorNum.struct = Tab.intType;
	}

	@Override
	public void visit(FactorChar factorChar) {
		factorChar.struct = Tab.charType;
	}

	@Override
	public void visit(FactorBool factorBool) {
		factorBool.struct = TabExtended.boolType;
	}

	@Override
	public void visit(NewArray newArray) {
		if (newArray.getExpr().struct != Tab.intType) {
			newArray.struct = Tab.noType;
			report_error("New Array: tip Expr (" + structName(newArray.getExpr().struct) + ") mora biti int",
					newArray);
		}
		newArray.struct = new Struct(Struct.Array, newArray.getType().struct);
	}

	@Override
	public void visit(FactorExpr factorExpr) {
		factorExpr.struct = factorExpr.getExpr().struct;
	}
	// Designator -----------------------------------------------------------------
	
	@Override
	public void visit(DesigWithExpr desigWithExpr) {
		Struct e = desigWithExpr.getExpr().struct;
		if (e != Tab.intType) {
			report_error("Expr (" + structName(e) + ") mora biti niz", desigWithExpr);
			desigWithExpr.obj = Tab.noObj;
			return;
		}
		desigWithExpr.obj = new Obj(Obj.Elem, desigWithExpr.getPreDesignator().obj.getName() , desigWithExpr.getPreDesignator().obj.getType().getElemType());
		report_info("Pristup nizu: " + desigWithExpr.getPreDesignator().obj.getName(), desigWithExpr);
	}
	
	@Override
	public void visit(DesigWithoutExpr desigWithoutExpr) {
		desigWithoutExpr.obj = desigWithoutExpr.getPreDesignator().obj;
	}
	
	@Override
	public void visit(WithDC withDC) {
		String ns = withDC.getName();
		String nsVar = withDC.getSubName();
		String fullName = ns + "::"+nsVar;
		Obj nsD = Tab.find(fullName);
		if(nsD == Tab.noObj) {
			report_error("Iskorisceno namespace polje ("+fullName+") ne postoji", withDC);
			withDC.obj = Tab.noObj;
			return;
		}
		withDC.obj = nsD;
		
	}
	
	@Override
	public void visit(WithoutDC withoutDC) {
		if(namespScope) {
			Obj d = Tab.find(currNamespaceStr + "::" + withoutDC.getName());
			if (d == Tab.noObj) {
				Obj d1 = Tab.find(withoutDC.getName());
				if (d1 == Tab.noObj) {
					report_error("Promenljiva (" + withoutDC.getName() + ") nije deklarisana", withoutDC);
				}
				withoutDC.obj = d1;
				return;
			}
			withoutDC.obj = d;
		}
		else {
			Obj d = Tab.find(withoutDC.getName());
			if (d == Tab.noObj) {
				report_error("Promenljiva (" + withoutDC.getName() + ") nije deklarisana", withoutDC);
			}
			withoutDC.obj = d;
		}
	}


	// -----------------------------------------------------------------
	@Override
	public void visit(EqualOper equalOper) {
		relOp = 1;
	}

	@Override
	public void visit(NotEqualOp NotEqualOp) {
		relOp = 2;
	}

	@Override
	public void visit(LessOp LessOp) {
		relOp = 3;
	}

	@Override
	public void visit(GreaterOp GreaterOp) {
		relOp = 4;
	}

	@Override
	public void visit(LessEqOp LessEqOp) {
		relOp = 5;
	}

	@Override
	public void visit(GreaterEqOp GreaterEqOp) {
		relOp = 6;
	}

	@Override
	public void visit(PlusOper PlusOper) {
		addOp = 1;
	}

	@Override
	public void visit(MinusOper MinusOper) {
		addOp = 2;
	}

	@Override
	public void visit(MulOper MulOper) {
		mulOp = 1;
	}

	@Override
	public void visit(DivOper DivOper) {
		mulOp = 2;
	}

	@Override
	public void visit(ModuoOper ModuoOper) {
		mulOp = 3;
	}

	public boolean passed() {
		return !errorDetected;
	}
}