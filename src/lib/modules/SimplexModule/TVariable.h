/**
 * @file TVariable.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */
 
#include "../../Common.h"
#include "TRational.h"


namespace smtrat
{

	class TVariable{


	private:

				//algorithm depends on an order of the variables
		int id=0;

				//A TVariable is either connected to a Variable in the formula or to a formula
		carl::Variable original;
		FormulaT formula;

		TRational value;

				//Is stored after succesful check, to reset for backtrace
		TRational lastValue;

		//The actual bounds for this variable
		TRational upperBound;

		TRational lowerBound;
		
		//The bounds for the formula, are used to set the actual bounds when activated
		TRational* upperBoundFormula = nullptr;
		
		TRational* lowerBoundFormula = nullptr;


		bool isBasic;

		bool isSlack;

				//Allows fast access to the position, used to get values in the tableau matrix for variables
		int positionMatrixX=-1;
		int positionMatrixY=-1;


	public:

		TVariable();

		//Constructor for slack variables
		TVariable(FormulaT formula, int pId, bool pIsBasic);

		//Constructor for original variables
		TVariable(carl::Variable pOriginal, int pId, bool pIsBasic);


		void activateUpperBound(bool status);
		void activateLowerBound(bool status);

		int getId() { return id; };

		bool getIsBasic(){return isBasic; };
		void setIsBasic(bool basic){this->isBasic = basic;}

		TRational& getValue() { return value; };
		void setValue(TRational r) { value = r; };

				//Stores and load the value
		void saveValue();
		void loadValue();

		void setPositionMatrixX(int positionMatrixX) {this->positionMatrixX = positionMatrixX;}
		void setPositionMatrixY(int positionMatrixY) {this->positionMatrixY = positionMatrixY;}
		int getPositionMatrixX() {return positionMatrixX;}
		int getPositionMatrixY() {return positionMatrixY;}

		TRational& getUpperBound() { return upperBound; };
		TRational& getLowerBound() { return lowerBound; };
		
		void setUpperBoundFormula(TRational* bound){ upperBoundFormula = bound;}
		void setLowerBoundFormula(TRational* bound){ lowerBoundFormula = bound;}
		
		bool hasUpperBoundFormula(){return upperBoundFormula != nullptr;}
		bool hasLowerBoundFormula(){return lowerBoundFormula != nullptr;}

		FormulaT& getFormula() { return formula; };

		std::string getName();

		/**
		 * Takes a bound and returns a value for delta that this variable still fullfills this bound 
		 */
		Rational calculateDelta(TRational b);
	};
}