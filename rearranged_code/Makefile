CC=COQC
.PHONY: all
all: prelims.vo repeater.vo increasing_expanding.vo  inverse.vo countdown.vo applications.vo inv_ack.vo

prelims.vo: prelims.v
	$(CC) prelims.v

repeater.vo: prelims.vo repeater.v
	$(CC) repeater.v

increasing_expanding.vo: repeater.vo increasing_expanding.v
	$(CC) increasing_expanding.v

inverse.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.v
	$(CC) inverse.v

countdown.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.vo countdown.v
	$(CC) countdown.v

applications.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.vo countdown.vo  applications.v
	$(CC) applications.v

inv_ack.vo: prelims.vo repeater.vo increasing_expanding.vo inverse.vo countdown.vo  applications.vo inv_ack.v
	$(CC) inv_ack.v

.PHONY: clean
clean:
	rm -f *.vo *.glob
