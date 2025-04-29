CHAPTER_DIR := ../LeanBook/Chapters

MD_DIR := src

NAMES :=  Connectives \
          CurryHoward \
          Equality \
          FirstOrderLogic \
		  Hierarchies \
          InductiveTypes \
		  Introduction \
		  LambdaCalculus \
		  Lean \
		  Numbers \
		  PropositionalLogic \
		  Quotients \
		  Reals \
		  SUMMARY \
		  Tactics

MD_FILES := $(foreach item,$(NAMES), $(MD_DIR)/$(item).md)

all: $(MD_FILES)

$(MD_DIR)/%.md: $(CHAPTER_DIR)/%.lean
	python3 dm.py $(CHAPTER_DIR)/$*.lean > $@

clean:
	rm $(MD_DIR)/*.md
