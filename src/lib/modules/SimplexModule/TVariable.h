#include <stack>
#include "../../Common.h"
#include "Bound.h"
#include <limits>


namespace smtrat
{

	class TVariable{


	private:

		int id=0;

				//A TVariable is either connected to a Variable in the formula or to a formula
		carl::Variable original;
		FormulaT formula;

		TRational value;

				//Is stored after succesful check, to reset for backtrace
		TRational lastValue;


		TRational upperBound;

		TRational lowerBound;


		bool isBasic;

		bool isSlack;

				//used in the method that finds the "problem set" of formulas
				//helps to create the sets N- and N+ as described in the paper
		int positionMatrixX=-1;
		int positionMatrixY=-1;


	public:

		TVariable();

		TVariable(FormulaT formula, int pId, bool pIsBasic);

		TVariable(carl::Variable pOriginal, int pId, bool pIsBasic);

		void changeUpperBound(TRational b);

		void changeLowerBound(TRational b);

		int getId() { return id; };

		bool getIsBasic(){return isBasic; };
		void setIsBasic(bool basic){this->isBasic = basic;}

		TRational& getValue() { return value; };
		void setValue(TRational r) { value = r; };

				//Stores and load value/bounds
		void saveValue();
		void load();

		void setPositionMatrixX(int positionMatrixX) {this->positionMatrixX = positionMatrixX;}
		void setPositionMatrixY(int positionMatrixY) {this->positionMatrixY = positionMatrixY;}
		int getPositionMatrixX() {return positionMatrixX;}
		int getPositionMatrixY() {return positionMatrixY;}

		TRational& getUpperBound() { return upperBound; };
		TRational& getLowerBound() { return lowerBound; };

		FormulaT& getFormula() { return formula; };

		std::string getName();

		Rational calculateDelta(TRational b);
	};
}