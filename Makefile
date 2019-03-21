CC=COQC

.PHONY: all
all: prelims.vo countdown_repeater.vo \
	inverse.vo applications.vo \
	inv_ack.vo inv_ack_hier.vo

prelims.vo: prelims.v
	$(CC) prelims.v

countdown_repeater.vo: prelims.vo countdown_repeater.v
	$(CC) countdown_repeater.v

inverse.vo: prelims.vo countdown_repeater.vo inverse.v
	$(CC) inverse.v

applications.vo: prelims.vo countdown_repeater.vo inverse.vo applications.v
	$(CC) applications.v

inv_ack.vo: prelims.vo countdown_repeater.vo inverse.vo applications.vo inv_ack.v
	$(CC) inv_ack.v

inv_ack_hier.vo: inv_ack_hier.v
	$(CC) inv_ack_hier.v

.PHONY: paper
paper:
	cd paper; pdflatex inv-ack.tex; cd -


.PHONY: clean
clean:
	rm -f *.vo *.glob paper/*.pdf paper/*.aux paper/*.log paper/*.out paper/*.spl
